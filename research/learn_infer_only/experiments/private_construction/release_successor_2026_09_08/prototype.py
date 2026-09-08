"""Symbolic MIFE transcript compiler, NOT an encryption or obfuscation implementation.

The oracle below is a test semantics with a private plaintext table. Python object
access does not protect that table; its ideal boundary is not a deployment claim.
The separately stated theorem uses the real source FE game, not these handles.
"""
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path

REJECT = 'reject'
OBS = (None, (0,-1), (0,1), (1,-1), (1,1))

def step(state, observation):
    if observation is None:
        return state
    i,y = observation
    result = list(state)
    if (result[i] >= 0) != (y == 1):
        result[i] += y
    return tuple(result)

@dataclass(frozen=True)
class Contract:
    horizon: int
    @property
    def bound(self): return self.horizon + 2
    @property
    def scalar_bits(self): return (2*self.bound).bit_length()
    @property
    def input_bits(self):
        return max(2*self.scalar_bits, (2*(self.horizon+1)-1).bit_length(), 3)
    def initial(self, state):
        assert all(-self.bound <= z <= self.bound for z in state)
        return (state[0]+self.bound) + ((state[1]+self.bound) << self.scalar_bits)
    def parse_initial(self, value):
        low = value & ((1 << self.scalar_bits)-1)
        high = value >> self.scalar_bits
        if not (0 <= low <= 2*self.bound and 0 <= high <= 2*self.bound):
            return None
        return low-self.bound, high-self.bound
    def replay(self, values):
        assert len(values) == self.horizon+2
        if any(not isinstance(v,int) or not 0 <= v < 2**self.input_bits for v in values):
            return REJECT
        state = self.parse_initial(values[0])
        selector = values[-1]
        if state is None or selector >= 2*(self.horizon+1): return REJECT
        if any(v >= len(OBS) for v in values[1:-1]): return REJECT
        t,query = divmod(selector,2)
        for encoded in values[1:t+1]: state = step(state,OBS[encoded])
        return int(state[query] >= 0)

@dataclass(frozen=True)
class Cipher:
    slot: int
    label: str

class SymbolicOracle:
    """Trusted *ideal* semantics; no claimed software secrecy for these fields."""
    def __init__(self, contract, initial):
        self.contract = contract
        self._messages = {}
        self._serial = 0
        self._anchor_issuance = True
        self.anchor = self._encode(0,contract.initial(initial))
        self._anchor_issuance = False
        # These are the entire surviving interface capabilities in the model.
        self.public_encryption_slots = tuple(range(1,contract.horizon+2))
        self.function_keys = ('replay_classification',)
    def _encode(self, slot, value):
        self._serial += 1
        label = 'symbolic-cipher-%08d' % self._serial
        self._messages[label] = (slot,value)
        return Cipher(slot,label)
    def encrypt(self, slot, value):
        assert slot in self.public_encryption_slots
        return self._encode(slot,value)
    def release(self, key, ciphertexts):
        assert key in self.function_keys
        assert len(ciphertexts) == self.contract.horizon+2
        values = []
        for i,c in enumerate(ciphertexts):
            slot,value = self._messages[c.label]
            assert c.slot == slot == i
            values.append(value)
        return self.contract.replay(values)

@dataclass(frozen=True)
class Resident:
    anchor: Cipher
    observations: tuple
    used: int
    def learn(self, oracle, observation):
        assert self.used < oracle.contract.horizon
        code = OBS.index(observation)
        new = oracle.encrypt(self.used+1,code)
        cells = self.observations[:self.used] + (new,) + self.observations[self.used+1:]
        return Resident(self.anchor,cells,self.used+1), 'ack'
    def infer(self, oracle, query, prefix=None):
        if prefix is None: prefix = self.used
        assert 0 <= prefix <= oracle.contract.horizon and query in (0,1)
        selector = oracle.encrypt(oracle.contract.horizon+1,2*prefix+query)
        return oracle.release('replay_classification',(self.anchor,)+self.observations+(selector,))

def initialize(contract, initial):
    oracle = SymbolicOracle(contract,initial)
    cells = tuple(oracle.encrypt(i,0) for i in range(1,contract.horizon+1))
    return oracle, Resident(oracle.anchor,cells,0)

def direct(initial, observations, prefix, query):
    # Independent reference: no call to step or Contract.replay.
    state = list(initial)
    for obs in observations[:prefix]:
        if obs is None: continue
        i,label = obs
        wrong = (state[i] < 0 and label == 1) or (state[i] >= 0 and label == -1)
        state[i] = state[i] + (label if wrong else 0)
    return int(state[query]>=0),tuple(state)

def audit():
    c = Contract(4)
    # Exhaustive correctness on the full valid initial and record space.
    correct = 0
    for initial in product(range(-c.bound,c.bound+1),repeat=2):
        for codes in product(range(5),repeat=c.horizon):
            observations = [OBS[z] for z in codes]
            for t in range(c.horizon+1):
                for q in (0,1):
                    got = c.replay((c.initial(initial),)+codes+(2*t+q,))
                    want,_ = direct(initial,observations,t,q)
                    assert got == want
                    correct += 1
    # Fresh challenge label at each possible position; every valid public
    # replacement of all other slots, every permitted prefix and output.
    private_label_checks = 0
    initial = (0,c.horizon+1)
    for j in range(c.horizon):
        for rest in product(range(5),repeat=c.horizon-1):
            a = list(rest); a.insert(j,3) # hidden negative observation in lane 1
            b = list(rest); b.insert(j,4) # hidden positive observation in lane 1
            for t in range(c.horizon+1):
                for q in (0,1):
                    assert c.replay((c.initial(initial),)+tuple(a)+(2*t+q,)) == c.replay((c.initial(initial),)+tuple(b)+(2*t+q,))
                    private_label_checks += 1
    initial_pair_checks = 0
    for codes in product(range(5),repeat=c.horizon):
        for selector in range(2*(c.horizon+1)):
            assert c.replay((c.initial((0,5)),)+codes+(selector,)) == c.replay((c.initial((0,6)),)+codes+(selector,))
            initial_pair_checks += 1
    # Complete byte-domain parsing reduces every malformed plaintext field to
    # one common reject. These are function inputs, never malformed ciphertexts.
    parse_checks = 0
    base = [c.initial(initial)] + [0]*c.horizon + [0]
    for slot in range(1,c.horizon+2):
        valid = 5 if slot <= c.horizon else 2*(c.horizon+1)
        for value in range(valid,2**c.input_bits):
            row = base.copy(); row[slot] = value
            assert c.replay(tuple(row)) == REJECT
            parse_checks += 1
    # Real continuing operations in the ideal FE semantics, all 32 observation
    # and selector credentials are available before the first observation.
    big = Contract(32)
    traces = []; final_private = []
    for private_label in (-1,1):
        o,r = initialize(big,(0,33))
        assert 0 not in o.public_encryption_slots and not o._anchor_issuance
        trace = []; observations = []; snapshots = [r]
        for t in range(32):
            obs = (1,private_label) if t == 5 else ((0,-1 if t%2==0 else 1) if t%3 else (1,-1))
            observations.append(obs)
            r,ack = r.learn(o,obs); snapshots.append(r)
            got = [r.infer(o,q) for q in (0,1)]
            want = [direct((0,33),observations,t+1,q)[0] for q in (0,1)]
            assert got == want
            trace.append({'step':t+1,'ack':ack,'classes':got})
        assert r.used == 32 and r.anchor == snapshots[0].anchor
        # Archived prefixes and a legitimate fork remain reusable.
        old = snapshots[2]
        fork,ack = old.learn(o,(0,-1))
        assert fork.infer(o,0) == direct((0,33),observations[:2]+[(0,-1)],3,0)[0]
        assert old.infer(o,0) == direct((0,33),observations[:2],2,0)[0]
        traces.append(trace)
        final_private.append(direct((0,33),observations,32,1)[1])
    assert traces[0] == traces[1]
    assert final_private[0] != final_private[1]
    # The hidden label is semantically active and eventually observable under
    # an extended policy; it is not an ignored padding field.
    longer_negative = [(1,-1)] + [(1,-1)]*5
    longer_positive = [(1,1)] + [(1,-1)]*5
    beyond = [direct((0,5),seq,6,1)[0] for seq in (longer_negative,longer_positive)]
    assert beyond == [0,1]
    # Exposing a state-issuance capability changes the authorized function family.
    state_replacement = [direct((0,0),[(1,y)],1,1)[0] for y in (-1,1)]
    assert state_replacement == [0,1]
    nonlinear = [step((w,5),(0,-1))[0] for w in (-1,0,1)]
    assert nonlinear == [-1,-1,0]
    return {'claim':'EXECUTED symbolic/function checks only; no cryptographic implementation',
      'full_valid_domain_correctness_comparisons':correct,
      'fresh_private_label_robust_compatibility_comparisons':private_label_checks,
      'initial_state_robust_compatibility_comparisons':initial_pair_checks,
      'plaintext_parser_checks':parse_checks,
      'symbolic_worlds':2,'learn_per_world':32,'infer_per_world':66,
      'identical_released_traces':True,'final_semantic_states':final_private,
      'anchor_issuance_survives':False,'public_encryption_keys':33,'function_keys':1,
      'ciphertexts_in_current_resident':33,'selector_ciphertexts_per_infer':1,
      'valid_t4_input_bits':c.input_bits,'valid_t32_input_bits':big.input_bits,
      'visible_first_coordinate_changes':sum(traces[0][i]['classes'][0]!=traces[0][i-1]['classes'][0] for i in range(1,32)),
      'out_of_horizon_separation':beyond,'replacement_anchor_separation':state_replacement,
      'nonlinear_step_values':nonlinear,'trajectory':traces[0]}

if __name__ == '__main__':
    import time
    start = time.monotonic(); result = audit();result['elapsed_seconds'] = time.monotonic()-start
    here = Path(__file__).resolve().parent
    (here/'RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='trajectory'},indent=2))
