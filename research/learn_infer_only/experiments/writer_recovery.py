#!/usr/bin/env python3
"""[EXECUTED] Ideal-primitive GKS23 §6.2 writer exposure transcript.

NOT encryption. Handles are opaque to the modeled adversary; the simulator
stores their meanings. This models correctness/capabilities, not computational
security or function-size padding. In particular it does not invent a prefix
authenticator: same-setup, same-index element substitution is possible.
"""
from dataclasses import dataclass
import json


class Refused(Exception):
    pass


@dataclass(frozen=True)
class Handle:
    serial: int


class Ideal:
    def __init__(self):
        self.table = {}
        self.calls = {}

    def put(self, kind, value):
        h = Handle(len(self.table))
        self.table[h] = (kind, value)
        return h

    def get(self, h, kind):
        if h not in self.table or self.table[h][0] != kind:
            raise Refused("missing or wrong credential kind")
        return self.table[h][1]

    def call(self, name):
        self.calls[name] = self.calls.get(name, 0) + 1

    def fp_setup(self):
        return self.put("fp_msk", object())

    def inner_setup(self):
        return self.put("inner_msk", object())

    def issue_element(self, writer, i, x, tag):
        self.get(writer, "fp_msk")
        # FPFE.KeyGen(writer, H_{i,x,tag}); x is inside the ideal function key.
        return self.put("H_key", (writer, i, x, tag))

    def redirect(self, writer, inner, prf_key, beta=0, enc_state=None):
        self.get(writer, "fp_msk")
        self.get(inner, "inner_msk")
        if enc_state is not None:
            raise Refused("One-sFE.EncSetup returns bottom in this construction")
        self.call("FPFE.Enc")
        return self.put("fp_ct", (writer, inner, prf_key, beta))

    def evaluate_H(self, stored, redirected):
        writer, i, x, tag = self.get(stored, "H_key")
        writer2, inner, prf_key, beta = self.get(redirected, "fp_ct")
        self.call("FPFE.Dec")
        if writer != writer2:
            raise Refused("FPFE setup mismatch")
        if beta != 0:
            raise Refused("H's nonzero-beta branch returns bottom")
        # Symbolic PRF coins. All elements use this same valid inner setup.
        return self.put("inner_ct", (inner, i, x, (prf_key, tag)))

    def projection_key(self, inner):
        self.get(inner, "inner_msk")
        self.call("One-sFE.KeyGen")
        # The ONE function f*(state,x) = (bottom,x), used for the whole stream.
        return self.put("projection", inner)

    def read(self, projection, state, ciphertext):
        inner = self.get(projection, "projection")
        ct_inner, i, x, _coins = self.get(ciphertext, "inner_ct")
        self.call("One-sFE.Dec")
        expected = 1 if state is None else self.get(state, "reader_state")[1]
        if state is not None and self.get(state, "reader_state")[0] != inner:
            raise Refused("reader state belongs to another inner setup")
        if inner != ct_inner or i != expected:
            raise Refused("wrong inner setup or missing/repeated/out-of-order prefix")
        return x, self.put("reader_state", (inner, i + 1))


def recover(sim, exposed_writer, stored):
    inner = sim.inner_setup()
    redirected = sim.redirect(exposed_writer, inner, "attacker PRF key")
    key = sim.projection_key(inner)
    result, state = [], None
    for h in stored:
        ct = sim.evaluate_H(h, redirected)
        x, state = sim.read(key, state, ct)
        result.append(x)
    return result


def refuses(action):
    try:
        action()
    except Refused as e:
        return str(e)
    raise AssertionError("negative control unexpectedly succeeded")


def main():
    histories = values = 0
    example = None
    for length in range(1, 9):
        for seed in range(8):
            xs = [(53 * seed + 29 * i + i * i) % 256 for i in range(length)]
            sim = Ideal()
            writer = sim.fp_setup()
            stored = [sim.issue_element(writer, i + 1, x, f"tag-{i}")
                      for i, x in enumerate(xs)]
            recovered = recover(sim, writer, stored)
            assert recovered == xs
            assert sim.calls == {"FPFE.Enc": 1, "One-sFE.KeyGen": 1,
                                 "FPFE.Dec": length, "One-sFE.Dec": length}
            histories += 1
            values += length
            example = dict(length=length, original=xs, recovered=recovered,
                           calls=sim.calls)

    sim = Ideal()
    writer = sim.fp_setup()
    stored = [sim.issue_element(writer, i, 40 + i, f"tag-{i}") for i in (1, 2, 3)]
    inner = sim.inner_setup()
    redirect = sim.redirect(writer, inner, "k*")
    cts = [sim.evaluate_H(h, redirect) for h in stored]
    key = sim.projection_key(inner)
    _, after_first = sim.read(key, None, cts[0])
    controls = {
        "missing_writer": refuses(lambda: recover(sim, None, stored)),
        "wrong_writer": refuses(lambda: recover(sim, sim.fp_setup(), stored)),
        "beta_nonzero": refuses(lambda: sim.evaluate_H(
            stored[0], sim.redirect(writer, inner, "k*", beta=1))),
        "invalid_encoder_state": refuses(lambda: sim.redirect(writer, inner, "k*", enc_state=7)),
        "missing_first_element": refuses(lambda: sim.read(key, None, cts[1])),
        "repeat_first_element": refuses(lambda: sim.read(key, after_first, cts[0])),
        "skip_second_element": refuses(lambda: sim.read(key, after_first, cts[2])),
        "cross_inner_setup": refuses(lambda: sim.read(
            key, after_first, sim.evaluate_H(stored[1], sim.redirect(
                writer, sim.inner_setup(), "different k*")))),
    }
    # It would be an overclaim to say the primitive verifies the original history.
    substitute = sim.issue_element(writer, 2, 199, "alternate-tag")
    mixed = sim.evaluate_H(substitute, redirect)
    mixed_value, _ = sim.read(key, after_first, mixed)
    assert mixed_value == 199
    print(json.dumps(dict(
        label="EXECUTED ideal-primitive capability model; no cryptography",
        source="GKS23 2022/1599 §6.2 pp.57–58 Figures 8–9; Korb Fig.3.2 (via landed audit)",
        histories=histories, recovered_values=values,
        exposed=["FPFE.msk", "stored FPFE.sk_H_i for every required prefix index"],
        not_used=["outer FE.msk", "outer function key", "honest inner master secret"],
        example=example, negative_controls=controls,
        same_setup_same_index_substitution={"accepted": True, "output": mixed_value},
        scope="Single symbolic path only; failed controls do not prove secrecy."
    ), indent=2))


if __name__ == "__main__":
    main()
