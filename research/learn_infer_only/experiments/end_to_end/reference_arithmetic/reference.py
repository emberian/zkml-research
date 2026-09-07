#!/usr/bin/env python3
"""Independent, integer-only public BFV byte/arithmetic reference.

No production imports, executables, secret-key operations, plaintext recovery,
or ciphertext modification are used. Inputs are retained public synthetic CAS
objects; this reference computes expected public operation outputs in memory.
"""
from dataclasses import dataclass
import hashlib
import json

N = 4096
MODULI = (2199023190017, 4398046486529)
T = 4294828033
WIDTH = 577
MAGIC = b"RSBFV001"
PARAMS_ID = "fb16ccd74dd4b7bedb6673b369b56475af06f9415a4faf4645d411d3c7d0cda3"


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def varint(value):
    require(isinstance(value, int) and value >= 0, "unsigned varint")
    out = bytearray()
    while value >= 128:
        out.append((value & 127) | 128)
        value >>= 7
    out.append(value)
    return bytes(out)


def read_varint(data, offset):
    start, value = offset, 0
    for shift in range(0, 70, 7):
        require(offset < len(data), "truncated varint")
        byte = data[offset]
        offset += 1
        value |= (byte & 127) << shift
        if byte < 128:
            require(value < 2**64 and data[start:offset] == varint(value), "noncanonical varint")
            return value, offset
    raise ValueError("varint overflow")


def proto_fields(data):
    fields, offset = [], 0
    while offset < len(data):
        tag, offset = read_varint(data, offset)
        number, wire = tag >> 3, tag & 7
        require(number > 0, "zero protobuf field")
        if wire == 0:
            value, offset = read_varint(data, offset)
        elif wire == 2:
            length, offset = read_varint(data, offset)
            require(length <= len(data) - offset, "truncated protobuf field")
            value = data[offset:offset + length]
            offset += length
        else:
            raise ValueError("unsupported protobuf wire type")
        fields.append((number, wire, value))
    return fields


def field(number, wire, value):
    return varint(number * 8 + wire) + (varint(len(value)) + value if wire == 2 else varint(value))


def unpack_limb(data, modulus):
    bits = (modulus - 1).bit_length()
    require(len(data) == N * bits // 8, "wrong limb length")
    # Deliberately distinct from the source's streaming u128 transcode.
    integer = int.from_bytes(data, "little")
    mask = (1 << bits) - 1
    values = [(integer >> (bits * i)) & mask for i in range(N)]
    require(all(x < modulus for x in values), "noncanonical residue")
    return values


def pack_limb(values, modulus):
    require(len(values) == N and all(0 <= x < modulus for x in values), "invalid limb")
    bits = (modulus - 1).bit_length()
    integer = sum(x << (bits * i) for i, x in enumerate(values))
    return integer.to_bytes(N * bits // 8, "little")


def decode_poly(data):
    fields = proto_fields(data)
    require([x[:2] for x in fields] == [(1, 0), (2, 0), (3, 2), (4, 0)], "fixed polynomial fields")
    require(fields[0][2] == 2 and fields[1][2] == N and fields[3][2] == 1, "fixed polynomial metadata")
    raw = fields[2][2]
    offset, limbs = 0, []
    for modulus in MODULI:
        length = N * (modulus - 1).bit_length() // 8
        limbs.append(unpack_limb(raw[offset:offset + length], modulus))
        offset += length
    require(offset == len(raw), "trailing limb bytes")
    require(encode_poly(limbs) == data, "polynomial roundtrip")
    return limbs


def encode_poly(limbs):
    require(len(limbs) == 2, "two RNS limbs")
    raw = b"".join(pack_limb(limb, p) for limb, p in zip(limbs, MODULI))
    return field(1, 0, 2) + field(2, 0, N) + field(3, 2, raw) + field(4, 0, 1)


@dataclass
class Ciphertext:
    key_id: bytes
    components: list

    def encode(self):
        require(len(self.key_id) == 32 and len(self.components) == 2, "fixed ciphertext shape")
        payload = b"".join(field(1, 2, encode_poly(poly)) for poly in self.components)
        require(len(payload) == 85022, "fixed payload length")
        return MAGIC + b"\x01" + bytes.fromhex(PARAMS_ID) + self.key_id + len(payload).to_bytes(8, "little") + payload


def decode_ct(data):
    require(len(data) == 85103, "fixed ciphertext byte count")
    require(data[:9] == MAGIC + b"\x01", "ciphertext object only")
    require(data[9:41].hex() == PARAMS_ID, "fixed parameter identity")
    require(int.from_bytes(data[73:81], "little") == len(data) - 81, "wrapper payload length")
    fields = proto_fields(data[81:])
    require([x[:2] for x in fields] == [(1, 2), (1, 2)], "full unseeded level-zero ciphertext")
    ct = Ciphertext(data[41:73], [decode_poly(f[2]) for f in fields])
    require(ct.encode() == data, "ciphertext byte roundtrip")
    return ct


def decode_query(data):
    query = json.loads(data)
    require(set(query) == {"coefficients", "params_id", "schema"}, "fixed query fields")
    require(query["schema"] == "resident-public-query-v1" and query["params_id"] == PARAMS_ID, "query identity")
    values = query["coefficients"]
    require(len(values) == WIDTH and all(type(x) is int and -127 <= x <= 127 for x in values), "query range")
    require(json.dumps(query, sort_keys=True, separators=(",", ":")).encode() == data, "canonical query")
    return values


def learn(acc, fresh, old=None):
    require(acc.key_id == fresh.key_id and (old is None or old.key_id == acc.key_id), "key metadata equality")
    components = []
    for c in range(2):
        limbs = []
        for j, p in enumerate(MODULI):
            a, f = acc.components[c][j], fresh.components[c][j]
            o = old.components[c][j] if old else [0] * N
            limbs.append([(x + y - z) % p for x, y, z in zip(a, f, o)])
        components.append(limbs)
    return Ciphertext(acc.key_id, components)


def negacyclic_direct(a, b, modulus):
    """Integer schoolbook multiplication, then X^N=-1, then reduce mod p."""
    size = len(a)
    require(len(b) <= size, "polynomial degree")
    result = [0] * size
    for j, bj in enumerate(b):
        if bj:
            for i in range(size - j):
                result[i + j] += a[i] * bj
            for i in range(size - j, size):
                result[i + j - size] -= a[i] * bj
    return [x % modulus for x in result]


def primitive_root(modulus, size):
    """Independent deterministic root, not the production ChaCha-selected root."""
    require((modulus - 1) % (2 * size) == 0 and size & (size - 1) == 0, "root domain")
    for candidate in range(2, 10000):
        root = pow(candidate, (modulus - 1) // (2 * size), modulus)
        if pow(root, size, modulus) == modulus - 1:
            require(pow(root, 2 * size, modulus) == 1, "root order")
            return root
    raise ValueError("root search exhausted")


def bitrev(value, bits):
    return int(f"{value:0{bits}b}"[::-1], 2)


def cyclic_ntt(a, root, modulus):
    """Standard bit-reversed-input, ascending-stride Cooley-Tukey DFT."""
    size, bits = len(a), len(a).bit_length() - 1
    out = [a[bitrev(i, bits)] % modulus for i in range(size)]
    length = 2
    while length <= size:
        step = pow(root, size // length, modulus)
        for offset in range(0, size, length):
            omega = 1
            for j in range(length // 2):
                u = out[offset + j]
                v = out[offset + j + length // 2] * omega % modulus
                out[offset + j] = (u + v) % modulus
                out[offset + j + length // 2] = (u - v) % modulus
                omega = omega * step % modulus
        length *= 2
    return out


def negacyclic_ntt(a, b, modulus, psi=None):
    size = len(a)
    psi = psi or primitive_root(modulus, size)
    b = list(b) + [0] * (size - len(b))
    twist = [pow(psi, i, modulus) for i in range(size)]
    left = cyclic_ntt([x * y % modulus for x, y in zip(a, twist)], psi * psi % modulus, modulus)
    right = cyclic_ntt([x * y % modulus for x, y in zip(b, twist)], psi * psi % modulus, modulus)
    product = cyclic_ntt([x * y % modulus for x, y in zip(left, right)], pow(psi * psi, -1, modulus), modulus)
    inverse_n = pow(size, -1, modulus)
    return [x * inverse_n * pow(tw, -1, modulus) % modulus for x, tw in zip(product, twist)]


def source_indexed_forward(a, psi, modulus):
    """Handwritten modular equation model of native.rs's indexed schedule.

    It does not model machine-word lazy reductions, pointers, or execute Rust.
    """
    size, bits = len(a), len(a).bit_length() - 1
    out = [x % modulus for x in a]
    length, k = size // 2, 1
    while length:
        for offset in range(0, size, 2 * length):
            omega = pow(psi, bitrev(k, bits), modulus)
            k += 1
            for j in range(length):
                x, y = out[offset + j], out[offset + j + length] * omega % modulus
                out[offset + j], out[offset + j + length] = (x + y) % modulus, (x - y) % modulus
        length //= 2
    return out


def source_indexed_backward(a, psi, modulus):
    size, bits = len(a), len(a).bit_length() - 1
    out = list(a)
    length, k = 1, 0
    while length < size:
        for offset in range(0, size, 2 * length):
            omega = pow(psi, -(bitrev(k, bits) + 1), modulus)
            k += 1
            for j in range(length):
                x, y = out[offset + j], out[offset + j + length]
                out[offset + j], out[offset + j + length] = (x + y) % modulus, (x - y) * omega % modulus
        length *= 2
    return [x * pow(size, -1, modulus) % modulus for x in out]


def infer(acc, query, method=negacyclic_direct):
    reversed_query = list(reversed(query))
    return Ciphertext(acc.key_id, [[method(limb, reversed_query, p) for limb, p in zip(poly, MODULI)] for poly in acc.components])
