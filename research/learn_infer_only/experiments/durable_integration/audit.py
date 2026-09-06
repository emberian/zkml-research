#!/usr/bin/env python3
"""Finite public canonical-cell/durable schedule audit, not encryption or storage."""
from dataclasses import dataclass, replace
from pathlib import Path
import hashlib, json, subprocess, sys

@dataclass(frozen=True)
class Context:
    genesis: int = 7
    parent: int = 0
    program: int = 0
    version: int = 1
    command: int = 1
    authorization: int = 19
    recipient: int = 23
    randomness_rule: int = 0
    randomness_commitment: int = 0
    next: int = 1
    output: int = 1

@dataclass(frozen=True)
class Plan:
    tx: int = 91
    genesis_id: int = 7
    state_id: int = 22
    genesis: bytes = b'\1'
    pre: bytes = b'\0'
    post: bytes = b'\1'
    slot: int = 0
    context: Context = Context()

    @property
    def packet(self):
        return tuple(self.context.__dict__.values())

    @property
    def token(self):
        return self.genesis_id, self.slot

@dataclass(frozen=True)
class Store:
    genesis: bytes = b'\1'
    state: bytes = b'\0'
    consumed: tuple = ()
    budget: int = 10
    journal: tuple = ()

def root(data):
    return data[0] if data else 0

def opens(store, p):
    c = p.context
    return (p.genesis_id == 7 and p.state_id == 22
            and p.genesis == b'\1' and store.genesis == p.genesis
            and store.state == p.pre and c.genesis == p.genesis_id
            and c.parent == root(p.pre) and c.next == root(p.post)
            and p.slot == len(store.journal))

def preflight(store, p):
    if root(store.genesis) != root(p.genesis): return 'staleReadGuard'
    if root(store.state) != root(p.pre): return 'stalePreRoot'
    if p.token in store.consumed: return 'alreadyConsumed'
    if store.budget < 1: return 'insufficientBudget'
    return 'ready'

def install(store, p):
    return replace(store, state=p.post, consumed=store.consumed+(p.token,),
                   budget=store.budget-1, journal=store.journal+(p,))

def execute(store, p, crash=None):
    for recorded in store.journal:
        if recorded.tx == p.tx:
            if recorded != p: return store, 'transactionConflict', None, 0
            return store, 'replayed', recorded.packet, 0
    if not opens(store, p): return store, 'openingRefused', None, 0
    ready = preflight(store, p)
    if ready != 'ready': return store, ready, None, 0
    if crash == 'before': return store, 'crashBefore', None, 0
    after = install(store, p)
    if crash == 'after': return after, 'crashAfter', None, 1
    return after, 'accepted', after.journal[-1].packet, 1

def main():
    p, before = Plan(), Store()
    outcomes = {}
    after, status, packet, fresh = execute(before, p)
    assert status == 'accepted' and after.state == b'\1' and fresh == 1
    assert root(after.state) == p.context.next and p.token in after.consumed
    outcomes['materialized_install'] = dict(parent=list(before.state), post=list(after.state),
                                          installed_root=root(after.state), fresh=fresh)
    unchanged, status, packet, fresh = execute(before, p, 'before')
    assert unchanged == before and packet is None and fresh == 0
    outcomes['crash_before'] = dict(state_unchanged=True, packet_released=False)
    crashed, status, packet, fresh = execute(before, p, 'after')
    assert crashed == after and packet is None and fresh == 1
    retried, status, packet, fresh = execute(crashed, p)
    assert retried == after and status == 'replayed' and packet == p.packet and fresh == 0
    outcomes['crash_after_retry'] = dict(exact_packet=packet, fresh_on_retry=fresh,
                                       budget_after=after.budget, journal_entries=len(after.journal))
    again, status, duplicate, fresh = execute(after, p)
    assert status == 'replayed' and again == after and duplicate == p.packet and fresh == 0
    outcomes['duplicate_exact_packet'] = dict(same_packet=True, fresh=0)
    forged = replace(p, context=replace(p.context, recipient=999))
    assert execute(after, forged)[1] == 'transactionConflict'
    outcomes['recipient_substitution'] = 'transactionConflict'
    # The independently audited old helper accepted another Plan after the
    # genuine commit. The repaired helper reads only the committed journal.
    def old_release_helper(caller_plan, accepted_store):
        return caller_plan.packet
    def journal_release(accepted_store):
        return accepted_store.journal[-1].packet
    assert old_release_helper(forged, after) == forged.packet
    assert journal_release(after) == p.packet and journal_release(after) != forged.packet
    outcomes['release_helper_relabel'] = dict(old_recipient=999, journal_recipient=23)
    restored = replace(p, tx=92)
    assert execute(after, restored)[1] == 'openingRefused'
    assert execute(before, restored)[1] == 'accepted'
    outcomes['host_restore'] = 'openingRefused'
    outcomes['authority_rollback'] = 'accepted'
    colliding_genesis = replace(before, genesis=b'\1\x63')
    assert root(colliding_genesis.genesis) == root(before.genesis)
    assert preflight(colliding_genesis, p) == 'ready'
    assert execute(colliding_genesis, p)[1] == 'openingRefused'
    outcomes['equal_root_wrong_opening'] = dict(root_preflight='ready', exact_opening='refused')
    # Broken host: both workers retain the same read snapshot and perform
    # outward authorization from it before either installation becomes visible.
    cached = [opens(before, p) and preflight(before, p) == 'ready' for _ in range(2)]
    broken_packets = [p.packet for ready in cached if ready]
    safe_fresh = execute(before, p)[3] + execute(after, p)[3]
    assert len(broken_packets) == 2 and safe_fresh == 1
    outcomes['split_check_install_race'] = dict(broken_fresh=2, serialized_fresh=safe_fresh)
    result = dict(scope='public finite model; no cryptography or physical storage',
                  command=[sys.executable, str(Path(__file__).resolve())],
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  outcomes=outcomes)
    path = Path(__file__).parent/'results/audit.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
