"""Pure public SHAKE256 framing and capped accepted-field derivation.

No scalar exponents, CSPRNG, crypto backend, file access or secret inputs.
This concrete hash execution is not a proof of the ROM assumption.
"""
import hashlib
import json

CAP = 128
SEED = b"resident-designated-public-seed-positive-001"
SUITE = "SHAKE256-direct-bitwords-cap128-v1"
QUERY_PREFIX = b"resident-designated-public-seed-query-v1\x00"


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True, allow_nan=False).encode("ascii")


def frame(parts):
    """Injective list of length-prefixed byte strings, not a digest of D."""
    return QUERY_PREFIX + len(parts).to_bytes(4, "big") + b"".join(
        len(part).to_bytes(8, "big") + part for part in parts)


def query_bytes(descriptor_bytes, seed, role, coordinate, counter):
    return frame([descriptor_bytes, seed, role.encode("ascii"),
                  coordinate.to_bytes(4, "big"), counter.to_bytes(4, "big")])


def candidate(raw, bits):
    """Take the high bits. Raw bytes preserve every discarded low suffix bit."""
    assert len(raw) == (bits + 7) // 8
    return int.from_bytes(raw, "big") >> (8 * len(raw) - bits)


class SeedRejected(Exception):
    def __init__(self, partial):
        super().__init__("public seed exhausted its fixed rejection cap")
        self.partial = partial


def derive(descriptor, seed=SEED):
    assert descriptor["schema"] == "designated-complete-seed-domain-v1"
    assert descriptor["suite"] == SUITE and descriptor["rejection_cap"] == CAP
    assert type(seed) is bytes and seed == SEED  # one fixed normal candidate
    p, q = int(descriptor["p_hex"], 16), int(descriptor["q_hex"], 16)
    m, d = descriptor["row_count"], descriptor["dimension"]
    assert 1 <= m < d and p == 2*q+1
    assert len(descriptor["complete_registry"]) == m
    raw_domain = canonical(descriptor)
    result = {"suite": SUITE, "seed_hex": seed.hex(), "tau": [], "U": [], "tapes": []}
    for role, count, lower, upper in (("tau", m, 0, q), ("U", d-m, 1, p)):
        bits = (upper-1).bit_length()
        width = (bits+7)//8
        for index in range(count):
            tape = {"role": role, "coordinate": index, "word_bits": bits,
                    "raw_bytes_per_word": width, "discarded_low_bits": 8*width-bits,
                    "accepted_counter": None, "raw_words_hex": []}
            result["tapes"].append(tape)
            for counter in range(1, CAP+1):
                raw = hashlib.shake_256(query_bytes(raw_domain, seed, role, index, counter)).digest(width)
                tape["raw_words_hex"].append(raw.hex())
                value = candidate(raw, bits)
                if lower <= value < upper:
                    tape["accepted_counter"] = counter
                    result[role].append(value.to_bytes((p.bit_length()+7)//8, "big").hex())
                    break
            if tape["accepted_counter"] is None:
                raise SeedRejected(result)
    return result
