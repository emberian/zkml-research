#!/usr/bin/env python3
"""Executable public model of finality + independent head/consumption checks.

No encryption, proof system, network authentication or consensus implementation.
Finality check mirrors Kernel.FinalityGate.check. Votes cover an exact candidate.
The gate's metadata has no resident plaintext/decryption key. A separate public
arithmetic control stands in for the Stage-0 receipt, never for a private learner.
"""
from dataclasses import dataclass, replace, asdict
from fractions import Fraction
from itertools import product
import json


@dataclass(frozen=True)
class Context:
    genesis: int
    parent: int
    program: int
    version: int
    command: int
    authorization: int
    recipient: int
    randomness_rule: int
    randomness_commitment: int
    next: int
    output: int


@dataclass(frozen=True)
class Candidate:
    epoch: int
    prior: tuple[Context, ...]
    context: Context

    @property
    def log(self):
        return self.prior + (self.context,)


def prefix(a, b):
    return b[:len(a)] == a


class VoteBook:
    def __init__(self):
        self.votes = {0: [], 1: [], 2: []}

    def vote(self, candidate, nodes=(0, 1)):
        for node in nodes:
            if not all(prefix(old.log, candidate.log) or prefix(candidate.log, old.log)
                       for old in self.votes[node]):
                return False
        for node in nodes:
            self.votes[node].append(candidate)
        return True

    def check(self, candidate, voters=(0, 1)):
        # Closed core-quorum instance in FinalityGate. No online test on OLD votes.
        voters = set(voters)
        return {0, 1} <= voters and all(candidate in self.votes.get(n, []) for n in voters)


@dataclass(frozen=True)
class GateState:
    genesis: int = 7
    head: int = 1
    log: tuple[Context, ...] = ()
    consumed: frozenset[tuple[int, int]] = frozenset()


def authorize(state, book, candidate, manifest, delivered_recipient=23):
    c = candidate.context
    token = (c.genesis, len(candidate.prior))  # NOT a caller-selected nonce.
    checks = {
        'finality': book.check(candidate),
        'manifest_parent': manifest == (c.genesis, c.parent, len(candidate.prior)),
        'genesis': c.genesis == state.genesis,
        'current_prefix': candidate.prior == state.log,
        'current_head': c.parent == state.head,
        'unspent': token not in state.consumed,
        # Authoritative toy policy, not an attacker-supplied decision bit.
        'policy': (c.program, c.version, c.authorization, c.recipient) == (0, 1, 19, 23),
        'recipient_delivery': delivered_recipient == c.recipient,
        'deterministic_randomness': (c.randomness_rule, c.randomness_commitment) == (0, 0),
        'stage0_arithmetic_control': 0 <= c.parent < 2**256 and 0 <= c.command < 2**256
            and c.next == c.output == (c.parent + c.command) % 2**256,
    }
    if not all(checks.values()):
        return state, None, [name for name, ok in checks.items() if not ok]
    # Atomic authorization BEFORE delivery. Crash afterward may lose availability.
    updated = GateState(c.genesis, c.next, candidate.log, state.consumed | {token})
    return updated, (c.recipient, c.output), []


def make(state, command=2):
    z = (state.head + command) % 2**256
    return Candidate(0, state.log, Context(
        state.genesis, state.head, 0, 1, command, 19, 23, 0, 0, z, z))


def manifest(candidate):
    c = candidate.context
    return c.genesis, c.parent, len(candidate.prior)


def main():
    checks = {}
    state, book = GateState(), VoteBook()
    first = make(state)
    assert book.vote(first)
    after, delivery, denied = authorize(state, book, first, manifest(first))
    assert not denied and delivery == (23, 3)
    checks['honest_first_release'] = {'delivery': delivery}
    second = make(after, 4)
    assert book.vote(second)
    after2, delivery2, denied = authorize(after, book, second, manifest(second))
    assert not denied and delivery2 == (23, 7)
    checks['closed_second_transition'] = {'delivery': delivery2}

    assert book.check(first)  # The actual finality predicate is not freshness.
    _, repeated, reasons = authorize(after2, book, first, manifest(first))
    assert repeated is None and {'current_prefix', 'current_head', 'unspent'} <= set(reasons)
    checks['restore_old_manifest'] = dict(finality_still_true=True, refusal=reasons)
    # Rollback of the independent gate destroys its memory, without decrypting anything.
    _, repeated, reasons = authorize(state, book, first, manifest(first))
    assert repeated == (23, 3) and not reasons
    checks['rollback_gate_too'] = {'fresh_release_again': repeated}

    # A local quota can be restored arbitrarily many times (bounded witness here).
    local_snapshot = {'remaining': 1}
    local_releases = 0
    for _ in range(4):
        local = dict(local_snapshot)
        if local['remaining']:
            local['remaining'] -= 1
            local_releases += 1
    assert local_releases == 4
    checks['copyable_local_quota'] = {'quota': 1, 'releases': local_releases}

    # Every context field is in the vote identity; all one-field changes fail old votes.
    mutations = {}
    for field in Context.__dataclass_fields__:
        altered = replace(first, context=replace(first.context, **{field: getattr(first.context, field) + 1}))
        assert not book.check(altered)
        mutations[field] = 'refused by exact candidate vote identity'
    checks['old_receipt_context_substitutions'] = mutations

    # Stronger test: even after NEW votes, semantic/context checks must do their job.
    forged_parent = replace(first, context=replace(first.context, parent=5))
    new_book = VoteBook()
    assert new_book.vote(forged_parent)
    _, out, reasons = authorize(state, new_book, forged_parent, manifest(forged_parent))
    assert out is None and 'stage0_arithmetic_control' in reasons
    checks['rehash_and_revote_bad_parent'] = reasons
    _, out, reasons = authorize(state, book, first, manifest(first), delivered_recipient=24)
    assert out is None and reasons == ['recipient_delivery']
    checks['delivery_substitution'] = reasons
    assert not book.check(first, voters=(0,))
    checks['thin_quorum'] = 'refused'
    fork = replace(first, context=replace(first.context, command=4, next=5, output=5))
    assert not book.vote(fork)
    checks['incompatible_fork_vote'] = 'refused by prefix discipline'
    # Compromise: put votes for both forks in the book, violating the named premise.
    compromised = VoteBook()
    compromised.votes = {n: [first, fork] for n in range(3)}
    assert compromised.check(first) and compromised.check(fork)
    checks['compromised_vote_discipline'] = 'both conflicting candidates pass finality'
    # Host copies/advances state without asking gate: no release; no anti-copy claim.
    silent_branches = [(1 + d) % 2**256 for d in (2, 4)]
    assert silent_branches == [3, 5] and after2.log == (first.context, second.context)
    checks['silent_local_forks'] = {'possible_states': silent_branches, 'new_authorizations': 0}
    # A read-then-write split lets two stale observers each decide "fresh".
    a, oa, _ = authorize(state, book, first, manifest(first))
    b, ob, _ = authorize(state, book, first, manifest(first))
    assert oa == ob and a == b
    checks['non_atomic_check_then_install'] = 'two releases from the same before-state'
    # Freshness of a public seed does not stop selection among allowed seeds/forks.
    uniform = [bits[0] for bits in product((0, 1), repeat=2)]
    selected = [max(bits) for bits in product((0, 1), repeat=2)]
    p_base, p_selected = Fraction(sum(uniform), 4), Fraction(sum(selected), 4)
    assert p_base == Fraction(1, 2) and p_selected == Fraction(3, 4)
    checks['randomness_label_is_not_distribution'] = {
        'one_fair_draw': str(p_base), 'select_from_two_valid_draws': str(p_selected),
        'denominator': 'all four equally likely ordered pairs',
        'scope': 'selection-bias witness, not an attack on Stage-0 deterministic rule'}
    # Hole B: a modular product check deletes the quotient being certified.
    q, t, z = 17, 4, 3
    rounded = lambda value: (t * value + q // 2) // q
    assert z % q == (z + q) % q and rounded(z + q) == rounded(z) + t
    checks['integer_rescale_required'] = dict(Q=q, t=t, z=z,
        residue=z % q, y=rounded(z), shifted_y=rounded(z + q))
    print(json.dumps({'label': 'EXECUTED finite public model; no confidentiality claim',
                      'checks': checks, 'gate_fields': list(asdict(state))}, indent=2))


if __name__ == '__main__':
    main()
