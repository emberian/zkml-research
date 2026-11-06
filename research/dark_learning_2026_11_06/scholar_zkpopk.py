"""Exact bounded BFV relation and salted-hash Stern ZK reference backend.

Research only. Classical ROM Fiat--Shamir, 3-special soundness, no QROM theorem.
The verifier never receives encryption plaintext, secret key, or raw witness.
No lattice-hardness assertion for the deterministic toy BFV test parameters.

The optional linear backend target is LNS/LaZer; Stern is a deliberately expensive
fourth fallback that makes the exact same relation executable today. N=8192 is
COUNT-ONLY on the Mac. It is not a practical deployment recommendation.
"""
from __future__ import annotations
import copy
import hashlib
import json
import math
import random
import secrets
from dataclasses import dataclass

import bfv_ref as bfv

DOMAIN = "scholar-bfv-stern-v1"


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def digest(*parts):
    h = hashlib.sha256()
    for part in parts:
        s = canonical(part)
        h.update(len(s).to_bytes(8, "big")); h.update(s)
    return h.hexdigest()


def public_a(seed, N, Q):
    """Uniform rejection sampling from a pinned registry seed, in the XOF model.

    Registry, not prover, chooses this seed before key registration. This does not
    implement the distributed ceremony or prevent a dishonest registry grinding it.
    """
    width = (Q.bit_length() + 7) // 8
    limit = (1 << (8 * width)) // Q * Q
    a, ctr = [], 0
    while len(a) < N:
        block = hashlib.shake_256(canonical([DOMAIN, "key-a", seed, ctr])).digest(width)
        x = int.from_bytes(block, "big"); ctr += 1
        if x < limit:
            a.append(x % Q)
    return a


def rounds_for(bits):
    return math.ceil(bits / math.log2(3 / 2))


def challenges(statement, commitments, rounds, legacy=False):
    # The legacy mode is only a deliberately broken falsifier. All first-message
    # commitments must precede the SINGLE joint challenge vector.
    data = [DOMAIN, "challenge", statement] if legacy else [DOMAIN, "challenge", statement, commitments]
    raw = hashlib.shake_256(canonical(data)).digest(16 * rounds + 64)
    out = []
    for byte in raw:
        # Rejection rather than %3 prevents a biased trit distribution.
        if byte < 255:
            out.append(byte % 3)
            if len(out) == rounds:
                return out
    raise RuntimeError("XOF challenge rejection budget exhausted")


def swap_pairs(x, swaps):
    out = []
    for i, bit in enumerate(swaps):
        u, v = x[2*i:2*i+2]
        out.extend((v, u) if bit else (u, v))
    return out


def conv(a, b):
    return bfv.negacyclic_mul(a, b)[0]


@dataclass(frozen=True)
class Registry:
    N: int
    primes: tuple[int, ...]
    t: int
    seed: str
    key_id: str
    a: tuple[int, ...]
    b: tuple[int, ...]

    @property
    def Q(self):
        return math.prod(self.primes)

    def public(self):
        return dict(N=self.N, primes=list(self.primes), t=self.t, seed=self.seed,
                    key_id=self.key_id, a=list(self.a), b=list(self.b))

    def valid(self):
        return (self.N > 0 and self.N & (self.N-1) == 0 and self.t > 2 and self.t % 2 == 1
                and len(self.primes) == 3 and len(set(self.primes)) == 3
                and all(q > 2 and bfv.is_probable_prime(q) for q in self.primes)
                and bfv.is_probable_prime(self.t) and self.t not in self.primes
                and len(self.a) == len(self.b) == self.N
                and all(type(x) is int and 0 <= x < self.Q for x in self.a + self.b)
                and list(self.a) == public_a(self.seed, self.N, self.Q))


class Relation:
    """Linear map A over Z_(tQ), with a binary, pair-complement witness.

    Variables s,e_pk,m,eta have exact public intervals. Each shifted variable x
    and U-x is represented in bits; their sum equation enforces x <= U. Stern
    makes every bit binary. m is canonical in [0,t); eta is the *scaled phase*
    t*(c0+c1*s)-Q*m, bounded by t*8+(t-1)//2. Therefore every accepted relation
    ciphertext has exact-encoding error in [-8,8]. It does not certify the
    distribution of the key/error samples or application-specific zero padding.
    """
    def __init__(self, registry, ct, context):
        self.reg = registry
        N, Q, t = registry.N, registry.Q, registry.t
        self.N, self.mod = N, t*Q
        self.ct = tuple(tuple(c) for c in ct)
        if len(self.ct) != 2 or any(len(c) != N for c in self.ct):
            raise ValueError("ciphertext shape")
        if any(type(x) is not int or not 0 <= x < Q for c in self.ct for x in c):
            raise ValueError("noncanonical ciphertext")
        H = 8*t+(t-1)//2
        self.groups = (("s", -1, 1), ("e_pk", -8, 8), ("m", 0, t-1), ("eta", -H, H))
        self.spec, at = [], 0
        for name, lo, hi in self.groups:
            width = (hi-lo).bit_length()
            for i in range(N):
                self.spec.append((name, i, lo, hi, width, at))
                at += 2*width  # value bits and complement-to-upper-bound bits
        self.bit_count = at
        self.size = 2*at  # each bit paired with 1-bit for the Stern permutation
        # Linearization offsets: variables are decoded as lower + shifted bits.
        zeros = {name: [lo]*N for name,lo,hi in self.groups}
        const = self._equations(zeros)
        self.target = [(-x) % self.mod for x in const]
        self.target += [hi-lo for _,_,lo,hi,_,_ in self.spec]
        self.statement = dict(domain=DOMAIN, registry=registry.public(), ciphertext=[list(c) for c in ct],
                              context=context, intervals=[list(x) for x in self.groups],
                              bit_count=at, modulus=self.mod)

    def _equations(self, v):
        N, Q, t = self.N, self.reg.Q, self.reg.t
        key_prod = conv(list(self.reg.a), v["s"])
        ct_prod = conv(list(self.ct[1]), v["s"])
        keyeq = [t*(self.reg.b[i]+key_prod[i]+v["e_pk"][i]) for i in range(N)]
        cteq = [t*(self.ct[0][i]+ct_prod[i])-Q*v["m"][i]-v["eta"][i] for i in range(N)]
        return keyeq + cteq

    def apply(self, x):
        """Apply the public linear map; works for arbitrary masks modulo tQ."""
        if len(x) != self.size:
            raise ValueError("witness/mask shape")
        vals = {name: [0]*self.N for name,_,_ in self.groups}
        bounds = []
        for name, i, lo, hi, width, start in self.spec:
            a = sum((1<<j)*x[2*(start+j)] for j in range(width)) % self.mod
            b = sum((1<<j)*x[2*(start+width+j)] for j in range(width)) % self.mod
            vals[name][i] = a
            bounds.append((a+b) % self.mod)
        kp = conv(list(self.reg.a), vals["s"])
        cp = conv(list(self.ct[1]), vals["s"])
        t,Q = self.reg.t,self.reg.Q
        out = [t*(kp[i]+vals["e_pk"][i]) % self.mod for i in range(self.N)]
        out += [(t*cp[i]-Q*vals["m"][i]-vals["eta"][i]) % self.mod for i in range(self.N)]
        return out+bounds

    def witness(self, s, e_pk, m, eta):
        v = dict(s=s, e_pk=e_pk, m=m, eta=eta)
        if any(len(v[k]) != self.N for k,_,_ in self.groups):
            raise ValueError("private witness shape")
        bits = []
        for name,i,lo,hi,width,start in self.spec:
            value = v[name][i]
            if type(value) is not int or not lo <= value <= hi:
                raise ValueError(f"{name} outside exact interval")
            for z in (value-lo, hi-value):
                bits += [(z>>j)&1 for j in range(width)]
        x = [z for b in bits for z in (b, 1-b)]
        if self.apply(x) != self.target:
            raise ValueError("private witness does not satisfy key/ciphertext relation")
        return x


def _rng(rng):
    return rng if rng is not None else secrets.SystemRandom()


def _salt(rng):
    return rng.getrandbits(256).to_bytes(32, "big").hex()


def prove(rel, witness, soundness_bits=128, rng=None):
    rng = _rng(rng); reps = rounds_for(soundness_bits)
    if (len(witness) != rel.size or any(witness[2*i:2*i+2] not in ([0,1],[1,0])
                                      for i in range(rel.bit_count))
            or rel.apply(witness) != rel.target):
        raise ValueError("invalid binary relation witness")
    commits, states = [], []
    for k in range(reps):
        pi = [rng.randrange(2) for _ in range(rel.bit_count)]
        r = [rng.randrange(rel.mod) for _ in range(rel.size)]
        z = [(a+b) % rel.mod for a,b in zip(r,witness)]
        salts = [_salt(rng) for _ in range(3)]
        c = [digest(DOMAIN,k,0,salts[0],pi,rel.apply(r)),
             digest(DOMAIN,k,1,salts[1],swap_pairs(r,pi)),
             digest(DOMAIN,k,2,salts[2],swap_pairs(z,pi))]
        commits.append(c); states.append((pi,r,z,salts))
    ch = challenges(rel.statement, commits, reps)
    responses = []
    for c,(pi,r,z,salts) in zip(ch,states):
        if c == 0:
            responses.append(dict(c=c, pi=pi, v=r, salt0=salts[0], salt1=salts[1]))
        elif c == 1:
            responses.append(dict(c=c, pi=pi, v=z, salt0=salts[0], salt2=salts[2]))
        else:
            responses.append(dict(c=c, px=swap_pairs(witness,pi), v=swap_pairs(r,pi),
                                  salt1=salts[1], salt2=salts[2]))
    return dict(version=DOMAIN, soundness_bits=soundness_bits, commitments=commits, responses=responses)


def verify(rel, proof, soundness_bits=128, legacy=False):
    """Untrusted parser, public relation only. False with a reason on every error."""
    try:
        if not rel.reg.valid():
            return False,"key registry or pinned public a mismatch"
        reps = rounds_for(soundness_bits)
        if proof.get("version") != DOMAIN or proof.get("soundness_bits") != soundness_bits:
            return False,"proof/security profile mismatch"
        commits,responses = proof["commitments"],proof["responses"]
        if len(commits) != reps or len(responses) != reps:
            return False,"wrong repetition count"
        if any(len(row)!=3 or any(not isinstance(c,str) or len(c)!=64 for c in row) for row in commits):
            return False,"commitment shape"
        ch = challenges(rel.statement,commits,reps,legacy)
        for k,(c,C,R) in enumerate(zip(ch,commits,responses)):
            if type(R["c"]) is not int or R["c"] != c:
                return False,"Fiat-Shamir challenge mismatch"
            v = R["v"]
            if len(v)!=rel.size or any(type(a) is not int or not 0<=a<rel.mod for a in v):
                return False,"response shape/range"
            keys = ("salt0","salt1") if c==0 else (("salt0","salt2") if c==1 else ("salt1","salt2"))
            if any(not isinstance(R[s],str) or len(R[s])!=64 for s in keys):
                return False,"salt shape"
            if c in (0,1):
                pi = R["pi"]
                if len(pi)!=rel.bit_count or any(type(a) is not int or a not in (0,1) for a in pi):
                    return False,"permutation shape"
                av = rel.apply(v)
                if c==1:
                    av = [(a-b)%rel.mod for a,b in zip(av,rel.target)]
                if C[0] != digest(DOMAIN,k,0,R["salt0"],pi,av):
                    return False,"linear relation commitment mismatch"
                which = 1 if c==0 else 2
                if C[which] != digest(DOMAIN,k,which,R[f"salt{which}"],swap_pairs(v,pi)):
                    return False,"masked witness commitment mismatch"
            else:
                px = R["px"]
                if len(px)!=rel.size or any(type(a) is not int for a in px):
                    return False,"binary witness shape"
                if any(px[2*i:2*i+2] not in ([0,1],[1,0]) for i in range(rel.bit_count)):
                    return False,"pair is not a permuted bit/complement"
                if C[1] != digest(DOMAIN,k,1,R["salt1"],v):
                    return False,"masked witness commitment mismatch"
                z = [(a+b)%rel.mod for a,b in zip(v,px)]
                if C[2] != digest(DOMAIN,k,2,R["salt2"],z):
                    return False,"masked witness difference mismatch"
        return True,"accept"
    except (AttributeError,KeyError,TypeError,ValueError,IndexError,OverflowError):
        return False,"malformed proof"


def keygen(N, primes, t, seed, key_id="custodian-0", rng=None):
    rng = _rng(rng); Q=math.prod(primes)
    s=[rng.choice((-1,0,1)) for _ in range(N)]
    e=[rng.randint(-8,8) for _ in range(N)]
    a=public_a(seed,N,Q); az=conv(a,s)
    b=[(-x-y)%Q for x,y in zip(az,e)]
    reg=Registry(N,tuple(primes),t,seed,key_id,tuple(a),tuple(b))
    return reg,s,e


def encrypt_and_prove(reg,s,e_pk,m,context,soundness_bits=128,rng=None):
    """Produces a ciphertext envelope; recipient calls accept_ciphertext separately."""
    rng=_rng(rng); N,Q,t=reg.N,reg.Q,reg.t
    if len(m)!=N or any(type(x) is not int for x in m):
        raise ValueError("message shape")
    m=[x%t for x in m]
    a=[rng.randrange(Q) for _ in range(N)]
    e=[rng.randint(-8,8) for _ in range(N)]
    az=conv(a,s)
    enc=[(2*Q*x+t)//(2*t) for x in m]
    ct=([ (x-y-z)%Q for x,y,z in zip(enc,az,e)],a)
    eta=[t*(x-ee)-Q*mm for x,ee,mm in zip(enc,e,m)]
    rel=Relation(reg,ct,context)
    w=rel.witness(s,e_pk,m,eta)
    proof=prove(rel,w,soundness_bits,rng)
    return dict(ciphertext=[list(c) for c in ct],proof=proof)


def accept_ciphertext(reg,envelope,context,soundness_bits=128):
    """Fail-closed recipient gate. No secret key or plaintext accepted as argument."""
    try:
        rel=Relation(reg,envelope["ciphertext"],context)
        proof=envelope["proof"]
    except (KeyError,TypeError,ValueError):
        raise ValueError("ciphertext envelope refused: shape")
    ok,why=verify(rel,proof,soundness_bits)
    if not ok:
        raise ValueError("ciphertext envelope refused: "+why)
    return tuple(list(c) for c in rel.ct)


def multiply_verified(P,reg,envelope,context,soundness_bits=128):
    """Drop-in beside he_matvec.ptxct: admission always precedes P x ciphertext."""
    from he_matvec import ptxct
    return ptxct(P,accept_ciphertext(reg,envelope,context,soundness_bits),reg.Q)


def simulate_known_challenges(rel,soundness_bits=128,rng=None):
    """Attack: forge arbitrary false statement if challenges omit commitments.

    This is also the honest-verifier simulator's branch construction. It only
    passes the intentionally broken legacy verifier; no witness is supplied.
    """
    rng=_rng(rng); reps=rounds_for(soundness_bits)
    ch=challenges(rel.statement,[],reps,legacy=True)
    commitments,responses=[],[]
    for k,c in enumerate(ch):
        pi=[rng.randrange(2) for _ in range(rel.bit_count)]
        v=[rng.randrange(rel.mod) for _ in range(rel.size)]
        salts=[_salt(rng) for _ in range(3)]
        C=[_salt(rng) for _ in range(3)]
        if c in (0,1):
            av=rel.apply(v)
            if c==1: av=[(a-b)%rel.mod for a,b in zip(av,rel.target)]
            C[0]=digest(DOMAIN,k,0,salts[0],pi,av)
            which=1 if c==0 else 2
            C[which]=digest(DOMAIN,k,which,salts[which],swap_pairs(v,pi))
            R=dict(c=c,pi=pi,v=v,salt0=salts[0]); R[f"salt{which}"]=salts[which]
        else:
            px=[z for _ in range(rel.bit_count) for z in ((0,1) if rng.randrange(2) else (1,0))]
            C[1]=digest(DOMAIN,k,1,salts[1],v)
            C[2]=digest(DOMAIN,k,2,salts[2],[(a+b)%rel.mod for a,b in zip(v,px)])
            R=dict(c=c,px=px,v=v,salt1=salts[1],salt2=salts[2])
        commitments.append(C); responses.append(R)
    return dict(version=DOMAIN,soundness_bits=soundness_bits,commitments=commitments,responses=responses)


def counts(N,Q,t,soundness_bits=128):
    H=8*t+(t-1)//2
    bit_widths=dict(s=2,e_pk=5,m=(t-1).bit_length(),eta=(2*H).bit_length())
    B=2*N*sum(bit_widths.values())
    Mbits=(t*Q-1).bit_length()
    reps=rounds_for(soundness_bits)
    # Every branch: 2B residues; B bits (pair swaps or one bit per permuted pair);
    # two 256-bit opening salts. Commitments: three 256-bit hashes per repetition.
    wire_bytes=10+reps*(96+1+(2*B*Mbits+7)//8+(B+7)//8+64)
    body=8*wire_bytes
    return dict(N=N,statement_modulus_bits=Mbits,range_widths=bit_widths,
                binary_witness_bits=B,extended_witness_coordinates=2*B,repetitions=reps,
                classical_interactive_error_log2=reps*math.log2(2/3),
                compact_proof_bits=body,compact_proof_bytes=wire_bytes,
                caveat="compact codec count; Python JSON is larger; no QROM reduction")


def _pack_ints(xs,width):
    out=bytearray(); acc=nb=0
    for x in xs:
        if not 0<=x<(1<<width): raise ValueError("packing range")
        acc=(acc<<width)|x; nb+=width
        while nb>=8:
            nb-=8; out.append((acc>>nb)&255)
        acc &= (1<<nb)-1
    if nb: out.append(acc<<(8-nb))
    return bytes(out)


def _unpack_ints(data,width,count):
    out=[]; acc=nb=0
    for byte in data:
        acc=(acc<<8)|byte; nb+=8
        while nb>=width and len(out)<count:
            nb-=width; out.append((acc>>nb)&((1<<width)-1))
        acc &= (1<<nb)-1
    if len(out)!=count or acc: raise ValueError("packing length/padding")
    return out


def encode_proof(rel,proof):
    """Compact wire bytes. Commitments, masks and pair selectors have fixed sizes."""
    reps=rounds_for(proof["soundness_bits"])
    if len(proof["commitments"])!=reps or len(proof["responses"])!=reps:
        raise ValueError("proof shape")
    out=bytearray(b"SCHSTERN"+proof["soundness_bits"].to_bytes(2,"big"))
    for C in proof["commitments"]:
        for h in C: out.extend(bytes.fromhex(h))
    width=(rel.mod-1).bit_length()
    for R in proof["responses"]:
        c=R["c"]; out.append(c)
        out.extend(_pack_ints(R["v"],width))
        out.extend(_pack_ints(R["pi"] if c in (0,1) else R["px"][::2],1))
        for which in ((0,1) if c==0 else ((0,2) if c==1 else (1,2))):
            out.extend(bytes.fromhex(R[f"salt{which}"]))
    return bytes(out)


def decode_proof(rel,data,soundness_bits=128):
    """Public fixed-profile decoder; no dynamic allocation driven by packet lengths."""
    if not isinstance(data,bytes) or data[:10]!=b"SCHSTERN"+soundness_bits.to_bytes(2,"big"):
        raise ValueError("wire profile")
    reps=rounds_for(soundness_bits); width=(rel.mod-1).bit_length()
    vbytes=(rel.size*width+7)//8; pbytes=(rel.bit_count+7)//8
    want=10+reps*(96+1+vbytes+pbytes+64)
    if len(data)!=want: raise ValueError("wire length")
    at=10; C=[]; R=[]
    for _ in range(reps):
        C.append([data[at+32*j:at+32*(j+1)].hex() for j in range(3)]); at+=96
    for _ in range(reps):
        c=data[at]; at+=1
        if c not in (0,1,2): raise ValueError("wire challenge")
        v=_unpack_ints(data[at:at+vbytes],width,rel.size); at+=vbytes
        bits=_unpack_ints(data[at:at+pbytes],1,rel.bit_count); at+=pbytes
        rr=dict(c=c,v=v)
        if c in (0,1): rr["pi"]=bits
        else: rr["px"]=[z for bit in bits for z in (bit,1-bit)]
        for which in ((0,1) if c==0 else ((0,2) if c==1 else (1,2))):
            rr[f"salt{which}"]=data[at:at+32].hex(); at+=32
        R.append(rr)
    return dict(version=DOMAIN,soundness_bits=soundness_bits,commitments=C,responses=R)
