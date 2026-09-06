#!/usr/bin/env python3
"""Finite ideal commitment/proof/FE capability model; NOT cryptography or ZK."""
from __future__ import annotations

import hashlib
import json
import platform
import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Commitment:
    serial: int


@dataclass(frozen=True)
class Proof:
    serial: int


@dataclass(frozen=True)
class Packet:
    state: int
    opening: int
    commitment: Commitment
    proof: Proof


class IdealProvenance:
    """Explicit ideal relations and registries, no encryption or hiding proof.

    Honest proof generation is public and requires a satisfying witness.
    The signer/simulation capabilities intentionally bypass that relation.
    """
    def __init__(self, first_step="identity", parent_binding=True):
        self.first_step = first_step
        self.parent_binding = parent_binding
        self._commits = {}
        self._proofs = {}
        self.genesis, self.genesis_opening = self.commit(0)
        self.honest = self.prove_state(0, first_observation=0)

    def commit(self, state):
        c = Commitment(len(self._commits))
        r = 1000 + c.serial
        self._commits[c] = (state, r)
        return c, r

    def opens(self, c, state, r):
        return self._commits.get(c) == (state, r)

    def relation(self, state, first_observation):
        # The fixed H=2 witness carries the bounded history explicitly.
        expected = 0 if self.first_step == "identity" else first_observation % 256
        return state == expected

    def _make_proof(self, c, role):
        p = Proof(len(self._proofs))
        self._proofs[p] = (self.genesis, 1, c, role)
        return p

    def prove_state(self, state, first_observation=0):
        # Public prover: no secret signing credential is consulted.
        if not self.relation(state, first_observation):
            raise ValueError("the public witness does not satisfy descent")
        c, r = self.commit(state)
        return Packet(state, r, c, self._make_proof(c, "honest_relation"))

    def certify_arbitrary_state(self, state, exposed_credential):
        if exposed_credential not in {"unrestricted_state_signer", "false_proof_simulator"}:
            raise PermissionError("no arbitrary certification capability")
        c, r = self.commit(state)
        return Packet(state, r, c, self._make_proof(c, exposed_credential))

    def verify(self, packet):
        rec = self._proofs.get(packet.proof)
        return (rec is not None and rec[:3] == (self.genesis, 1, packet.commitment)
                and self.opens(packet.commitment, packet.state, packet.opening))

    def eval_learn(self, packet, private_x, encrypted_observation_parent, internal_guard=True):
        if internal_guard:
            if not self.verify(packet):
                return None
            if self.parent_binding and packet.commitment != encrypted_observation_parent:
                return None
        # The next protected state is kept as an ideal internal value.
        # Only its terminal high bit is returned here.
        return ((packet.state + private_x) % 256) >> 7


def binary_recover(probe):
    lo, hi, q = 0, 255, 0
    while lo < hi:
        mid = (lo + hi + 1) // 2
        answer = probe((128 - mid) % 256)
        if answer not in (0, 1):
            raise ValueError("probe was refused")
        q += 1
        if answer:
            lo = mid
        else:
            hi = mid - 1
    return lo, q


def run():
    model = IdealProvenance(parent_binding=False)
    refusals = 0
    for state in range(256):
        try:
            packet = model.prove_state(state)
        except ValueError:
            refusals += 1
        else:
            assert state == 0 and model.verify(packet)
    assert refusals == 255

    # Valid honest paths preserve uncertainty between x=0 and x=1.
    honest_answers = [model.eval_learn(model.honest, x, model.honest.commitment) for x in (0, 1)]
    assert honest_answers == [0, 0]

    # A genuine proof cannot be reused with an unrelated plaintext opening.
    opening_refusals = 0
    for state in range(1, 256):
        forged = Packet(state, model.honest.opening, model.honest.commitment, model.honest.proof)
        assert not model.verify(forged)
        opening_refusals += 1

    # An external verification wrapper can be bypassed using the exposed base key.
    wrapper_recovered = 0
    for secret in range(256):
        def external_wrapper_bypass(d):
            packet = Packet(d, model.honest.opening, model.honest.commitment, model.honest.proof)
            return model.eval_learn(packet, secret, model.honest.commitment, internal_guard=False)
        guess, probes = binary_recover(external_wrapper_bypass)
        assert guess == secret and probes == 8
        wrapper_recovered += 1

    # Exposed unrestricted signer, or hypothetical exposed false-proof simulator,
    # enables a reader in coalition with the public EK and restricted future keys.
    capability_recoveries = {}
    for credential in ("unrestricted_state_signer", "false_proof_simulator"):
        count = 0
        for secret in range(256):
            def cert_probe(d):
                packet = model.certify_arbitrary_state(d, credential)
                return model.eval_learn(packet, secret, model.honest.commitment)
            guess, probes = binary_recover(cert_probe)
            assert guess == secret and probes == 8
            count += 1
        capability_recoveries[credential] = count

    # Descent from genesis alone fails when a previous authorized Learn can
    # reach every known offset. These are TRUE proofs; no trapdoor is used.
    ancestry_only = IdealProvenance(first_step="learn", parent_binding=False)
    descent_only_recovered = 0
    for secret in range(256):
        def true_history_probe(d):
            packet = ancestry_only.prove_state(d, first_observation=d)
            return ancestry_only.eval_learn(packet, secret, ancestry_only.honest.commitment)
        guess, probes = binary_recover(true_history_probe)
        assert guess == secret and probes == 8
        descent_only_recovered += 1

    # Binding the fresh observation to its exact parent commitment excludes
    # these cross-history combinations, without adding a state-signing secret.
    bound = IdealProvenance(first_step="learn", parent_binding=True)
    mismatch_refusals = 0
    for d in range(256):
        other_parent = bound.prove_state(d, first_observation=d)
        assert bound.verify(other_parent)
        assert bound.eval_learn(other_parent, 173, bound.honest.commitment) is None
        mismatch_refusals += 1
    assert bound.eval_learn(bound.honest, 173, bound.honest.commitment) == 1

    # Binding commitment: a fixed statement cannot be opened to two states.
    valid0 = bound.opens(bound.genesis, 0, bound.genesis_opening)
    invalid1 = bound.opens(bound.genesis, 1, bound.genesis_opening)
    assert valid0 and not invalid1

    return {
        "not_encryption_not_zk": True,
        "public_prover_false_descent_refusals": refusals,
        "honest_private_input_answers": honest_answers,
        "copied_proof_wrong_opening_refusals": opening_refusals,
        "external_wrapper_bypass_recoveries": wrapper_recovered,
        "capability_recoveries_without_parent_binding": capability_recoveries,
        "true_ancestry_only_recoveries": descent_only_recovered,
        "probes_per_recovery": 8,
        "valid_wrong_parent_refusals": mismatch_refusals,
        "fixed_binding_genesis_opening_test": [valid0, invalid1],
        "important_scope": "parent-bound input is an ideal immutable encrypted field; no real authentication, nonmalleability, commitment, proof, or FE is implemented",
    }


def main():
    result = run()
    result["provenance"] = {
        "command": "python3 research/learn_infer_only/experiments/private_ingress/provenance/provenance_audit.py",
        "python": sys.version,
        "platform": platform.platform(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "provenance"}, indent=2))
    print("PASS: finite ideal provenance/capability witnesses; no cryptographic realization")


if __name__ == "__main__":
    main()
