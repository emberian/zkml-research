"""Executable fixed-coordinate ring prototype; no security certification.

R_q = Z_q[T]/(T^N+1). FLINT performs exact arbitrary-precision arithmetic.
The public setup never creates absent recipients' rows. Private coins/keys
are memory-only in the supplied runner; Python does not promise zeroization.
"""
from dataclasses import dataclass
import os
from flint import fmpz_mod_poly_ctx, fmpz_mat


def uniform_below(bound, count):
    """Independent OS-bit rejection; deliberately variable/expected time."""
    if bound <= 0 or count < 0:
        raise ValueError('positive bound, nonnegative count required')
    width = (bound-1).bit_length()
    size = max(1, (width+7)//8)
    mask = (1 << width)-1
    out = []
    while len(out) < count:
        want = min(8192, max(32, 2*(count-len(out))))
        data = os.urandom(want*size)
        for start in range(0, len(data), size):
            value = int.from_bytes(data[start:start+size], 'little') & mask
            if value < bound:
                out.append(value)
                if len(out) == count:
                    break
    return out


def center(value, modulus):
    value %= modulus
    return value if value <= modulus//2 else value-modulus


@dataclass(frozen=True)
class Parameters:
    N: int
    w: int
    d: int
    recipients: int
    p: int
    q: int
    sigma_key: int
    sigma_error: int
    flood: int
    W: int = 32
    denominator: int | None = None

    def __post_init__(self):
        if self.N < 16 or self.N & (self.N-1):
            raise ValueError('N must be a power of two at least 16')
        if not 0 < self.recipients < self.d or self.w < 3:
            raise ValueError('require 0 < recipients < d and w >= 3')
        if self.q % (2*self.N) != 1 or self.p % 2 != 1:
            raise ValueError('wrong modulus or plaintext parity')
        if self.D < 2*self.lift_bound+1:
            raise ValueError('encoding circle cannot hold declared lifts')
        if self.delta <= 2*self.W*self.error_bound:
            raise ValueError('deterministic cutoff correctness margin failed')

    @property
    def D(self):
        return self.denominator or (2*self.W*(self.p//2)+1)

    @property
    def delta(self):
        return self.q//self.D

    @property
    def lift_bound(self):
        return self.W*(self.p//2)

    @property
    def error_bound(self):
        return self.flood+self.w*self.N*(8*self.sigma_key)*(8*self.sigma_error)


class SparseBasis:
    """Invertible public B=I+C, C supported in first r rows/later columns.

    First r rows are the designated policy. C^2=0, hence B^-1=I-C.
    Every one of the d plaintext coordinates survives this bijection.
    """
    def __init__(self, d, recipients, p):
        self.d, self.r, self.p = d, recipients, p
        self.rows = []
        for i in range(recipients):
            self.rows.append([(j, c) for j, c in [(recipients+i, 2), (2*recipients+i, 3)] if j < d])

    def transform(self, x):
        if len(x) != self.d:
            raise ValueError('wrong input dimension')
        a = [value % self.p for value in x]
        for i, row in enumerate(self.rows):
            a[i] = (x[i]+sum(c*x[j] for j, c in row)) % self.p
        return [center(value, self.p) for value in a]

    def inverse(self, a):
        x = [value % self.p for value in a]
        for i, row in enumerate(self.rows):
            x[i] = (a[i]-sum(c*a[j] for j, c in row)) % self.p
        return x


class Ring:
    def __init__(self, N, q):
        self.N, self.q = N, q
        self.ctx = fmpz_mod_poly_ctx(q)

    def poly(self, coefficients):
        if len(coefficients) > self.N:
            raise ValueError('too many coefficients')
        return self.ctx(coefficients)

    def coefficients(self, poly):
        out = [int(x) for x in poly.coeffs()]
        return out+[0]*(self.N-len(out))

    def mul(self, a, b):
        product = a*b
        return product.truncate(self.N)-product.right_shift(self.N)

    @staticmethod
    def const_product(a, b):
        if len(a) != len(b):
            raise ValueError('different dimensions')
        return a[0]*b[0]-sum(x*y for x, y in zip(a[1:], reversed(b[1:])))


@dataclass
class RecipientKey:
    coordinate: int
    row: list


def generate_recipient_key(params, public_A, coordinate, sampler):
    """Recipient-local key generation; only the second return value is public.

    The same public A may be delivered to recipients on separate processes;
    this prototype's runner simulates those actors with distinct objects.
    """
    if not 0 <= coordinate < params.recipients:
        raise ValueError('coordinate is outside the fixed recipient policy')
    ring = Ring(params.N, params.q)
    row = [sampler.sample(params.sigma_key, params.N) for _ in range(params.w)]
    product = ring.ctx(0)
    for a, z in zip(public_A, row):
        product += ring.mul(a, ring.poly(z))
    return RecipientKey(coordinate, row), ring.coefficients(product)


@dataclass
class Ciphertext:
    c0: list
    h: list
    # A sufficient public L1 budget, tracked under linear combination.
    weight: int


class PublicSetup:
    def __init__(self, params, sampler):
        self.params, self.sampler = params, sampler
        self.ring = Ring(params.N, params.q)
        self.basis = SparseBasis(params.d, params.recipients, params.p)
        self.A = [self.ring.poly(uniform_below(params.q, params.N)) for _ in range(params.w)]
        self.P = [None]*params.d

    def register_public(self, coordinate, product):
        """Constructor accepts a public product; never receives a private row."""
        p, ring = self.params, self.ring
        if not 0 <= coordinate < p.recipients or self.P[coordinate] is not None:
            raise ValueError('invalid or duplicate registration')
        if len(product) != p.N or any(not 0 <= value < p.q for value in product):
            raise ValueError('noncanonical public product')
        self.P[coordinate] = list(product)

    def finish(self):
        if any(self.P[i] is None for i in range(self.params.recipients)):
            raise ValueError('recipient registrations incomplete')
        for i in range(self.params.recipients, self.params.d):
            self.P[i] = uniform_below(self.params.q, self.params.N)

    def encode(self, x):
        p, ring = self.params, self.ring
        if any(row is None for row in self.P):
            raise ValueError('setup incomplete')
        a = self.basis.transform(x)
        s = uniform_below(p.q, p.N)
        sp = ring.poly(s)
        c0 = []
        for public in self.A:
            e = self.sampler.sample(p.sigma_error, p.N)
            c0.append(ring.mul(public, sp)+ring.poly(e))
        floods = uniform_below(2*p.flood+1, p.d)
        h = [(ring.const_product(row, s)+f-p.flood+p.delta*value) % p.q
             for row, f, value in zip(self.P, floods, a)]
        return Ciphertext(c0, h, 1)

    def combine(self, terms):
        """Signed linear combination with declared L1 weight <= W."""
        p, ring = self.params, self.ring
        weight = sum(abs(c)*ct.weight for c, ct in terms)
        if weight > p.W:
            raise ValueError('combination exceeds declared coefficient window')
        c0 = [ring.ctx(0) for _ in range(p.w)]
        h = [0]*p.d
        for coefficient, ct in terms:
            if len(ct.c0) != p.w or len(ct.h) != p.d:
                raise ValueError('wrong ciphertext shape')
            for i, poly in enumerate(ct.c0):
                c0[i] += coefficient*poly
            for i, value in enumerate(ct.h):
                h[i] = (h[i]+coefficient*value) % p.q
        return Ciphertext(c0, h, weight)

    def phase(self, key, ct):
        dot = sum(self.ring.const_product(z, self.ring.coefficients(c))
                  for z, c in zip(key.row, ct.c0))
        return (ct.h[key.coordinate]-dot) % self.params.q

    def decode(self, key, ct):
        """Exact nearest actual Delta codepoint on the declared circle."""
        return self.decode_phase(self.phase(key,ct),ct.weight)

    def decode_phase(self, v, weight):
        p = self.params
        choices = set()
        for shift in (-1, 0, 1):
            floor = (v+shift*p.q)//p.delta
            for t in (floor, floor+1, -p.lift_bound, p.lift_bound):
                choices.add(max(-p.lift_bound, min(p.lift_bound, t)))
        distance = lambda t: abs(center(v-p.delta*t, p.q))
        ranked = sorted((distance(t), t) for t in choices)
        if len(ranked)>1 and ranked[0][0] == ranked[1][0]:
            raise ValueError('ambiguous nearest codepoint')
        if ranked[0][0] > weight*p.error_bound:
            raise ValueError('phase violates declared error budget')
        return ranked[0][1]


class RecipientBatch:
    """Private cache for a caller already holding the supplied recipient keys.

    The matrix contains exactly those rows, without absent-recipient rows.
    All products are exact integers. Ciphertext coefficient extraction and
    conversion are shared across readers; FLINT executes the batched dots.
    It is optional: PublicSetup.decode still supports one independent reader.
    """
    def __init__(self, setup, keys):
        p=setup.params
        if not keys:
            raise ValueError('at least one recipient key required')
        for key in keys:
            if not 0 <= key.coordinate < p.recipients or len(key.row) != p.w or any(len(z)!=p.N for z in key.row):
                raise ValueError('invalid recipient key shape')
        self.setup=setup
        self.coordinates=[key.coordinate for key in keys]
        self.matrix=fmpz_mat([[value for poly in key.row for value in poly] for key in keys])

    def phases(self, ct):
        p=self.setup.params
        if len(ct.c0)!=p.w or len(ct.h)!=p.d:
            raise ValueError('invalid ciphertext shape')
        transformed=[]
        for poly in ct.c0:
            coefficients=self.setup.ring.coefficients(poly)
            transformed.append(coefficients[0])
            transformed.extend(-value for value in reversed(coefficients[1:]))
        vector=fmpz_mat(p.w*p.N,1,transformed)
        products=self.matrix*vector
        return [(ct.h[coordinate]-int(products[i,0]))%p.q for i,coordinate in enumerate(self.coordinates)]

    def decode(self, ct):
        return [self.setup.decode_phase(v,ct.weight) for v in self.phases(ct)]


class Window:
    """Exact expiry retains original ciphertexts and bounds live L1 weight."""
    def __init__(self, setup, capacity):
        if not 1 <= capacity <= setup.params.W:
            raise ValueError('invalid window capacity')
        self.setup, self.capacity, self.queue = setup, capacity, []
        self.current = setup.combine([])

    def push(self, ct):
        if ct.weight != 1:
            raise ValueError('window accepts original fresh ciphertexts')
        # Operations first cancel the original outgoing ciphertext. The exact
        # queue identity, rather than a growing conservative history norm,
        # justifies resetting the live norm to len(queue).
        if len(self.queue) == self.capacity:
            outgoing = self.queue.pop(0)
            p = self.setup.params
            self.current.c0 = [a-b for a, b in zip(self.current.c0, outgoing.c0)]
            self.current.h = [(a-b)%p.q for a, b in zip(self.current.h, outgoing.h)]
            self.current.weight -= 1
        self.current = self.setup.combine([(1, self.current), (1, ct)])
        self.queue.append(ct)
        return self.current
