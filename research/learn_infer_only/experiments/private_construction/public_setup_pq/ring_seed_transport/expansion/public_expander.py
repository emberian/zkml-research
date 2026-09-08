"""[DERIVED] Public, indexed SHAKE256 row expansion with rejection into q.

The seed is public. This supplies reproducible bytes, not a hidden-seed PRG
claim. See SECURITY.md for the seeded-construction / random-oracle obligation.
"""
import hashlib
import time

PROTOCOL = b"ring-seed-transport/public-rows/v1"
CANDIDATES_PER_CHUNK = 1024
EXTRA_CHUNKS = 16
U64_LIMIT = 1 << 64


class ExpansionError(RuntimeError):
    pass


def _integer(value, name, *, minimum=0):
    if type(value) is not int or not minimum <= value < U64_LIMIT:
        raise ValueError(f"{name} must be an integer in [{minimum},2**64)")
    return value


def _lp(value):
    if len(value) >= (1 << 32):
        raise ValueError("domain field is too long")
    return len(value).to_bytes(4, "big") + value


def _family(value):
    if isinstance(value, str):
        value = value.encode("utf-8")
    if not isinstance(value, bytes) or not 1 <= len(value) <= 255:
        raise ValueError("family must encode to 1..255 bytes")
    return value


class PublicExpander:
    """PublicExpander(seed[32|64], binding[32]).row(family,index,N,q).

    binding is a parent-defined digest of noncircular profile/setup context.
    N and q are also bound explicitly. Instances perform no file I/O and draw
    no random bytes. last_stats/totals contain public aggregate work counters.
    """
    def __init__(self, seed: bytes, binding: bytes):
        if not isinstance(seed, bytes) or len(seed) not in (32, 64):
            raise ValueError("public seed must be exactly 32 or 64 bytes")
        if not isinstance(binding, bytes) or len(binding) != 32:
            raise ValueError("binding must be exactly 32 bytes")
        self.seed = seed
        self.binding = binding
        self._prefix = _lp(PROTOCOL) + _lp(seed) + _lp(binding)
        self.last_stats = {}
        self.totals = {"completed_rows": 0, "candidates_examined": 0,
                       "chunks_generated": 0, "xof_bytes_generated": 0}

    def row_domain(self, family, index, N, q):
        """Canonical public row-domain bytes, without the final chunk index."""
        family = _family(family)
        index = _integer(index, "index")
        N = _integer(N, "N", minimum=1)
        if type(q) is not int or q < 2:
            raise ValueError("q must be an integer at least two")
        q_bytes = q.to_bytes((q.bit_length() + 7) // 8, "big")
        return (self._prefix + _lp(family) + index.to_bytes(8, "big") +
                N.to_bytes(8, "big") + _lp(q_bytes))

    @staticmethod
    def _chunk(domain, chunk_index, word_bytes):
        address = domain + _integer(chunk_index, "chunk index").to_bytes(8, "big")
        return hashlib.shake_256(address).digest(CANDIDATES_PER_CHUNK * word_bytes)

    def row(self, family, index, N, q):
        start = time.perf_counter()
        domain = self.row_domain(family, index, N, q)
        bits = (q - 1).bit_length()
        word_bytes = (bits + 7) // 8
        mask = (1 << bits) - 1
        max_chunks = (4 * N + CANDIDATES_PER_CHUNK - 1) // CANDIDATES_PER_CHUNK + EXTRA_CHUNKS
        result = []
        append = result.append
        examined = chunks = 0
        for chunk_index in range(max_chunks):
            data = self._chunk(domain, chunk_index, word_bytes)
            if len(data) != CANDIDATES_PER_CHUNK * word_bytes:
                raise ExpansionError("candidate chunk has unexpected length")
            chunks += 1
            for offset in range(0, len(data), word_bytes):
                candidate = int.from_bytes(data[offset:offset + word_bytes], "little") & mask
                examined += 1
                if candidate < q:
                    append(candidate)
                    if len(result) == N:
                        elapsed = time.perf_counter() - start
                        self.last_stats = {
                            "row_index": index, "N": N, "q_bits": q.bit_length(),
                            "candidate_bits": bits, "candidate_bytes": word_bytes,
                            "candidates_examined": examined,
                            "rejections": examined - N,
                            "chunks_generated": chunks, "max_chunks": max_chunks,
                            "xof_bytes_generated": chunks * CANDIDATES_PER_CHUNK * word_bytes,
                            "unused_candidate_bytes": (chunks * CANDIDATES_PER_CHUNK - examined) * word_bytes,
                            "seconds": elapsed, "completed": True,
                        }
                        self.totals["completed_rows"] += 1
                        for name in ("candidates_examined", "chunks_generated", "xof_bytes_generated"):
                            self.totals[name] += self.last_stats[name]
                        return result
        self.last_stats = {"row_index": index, "N": N, "q_bits": q.bit_length(),
                           "candidates_examined": examined, "chunks_generated": chunks,
                           "max_chunks": max_chunks, "completed": False,
                           "xof_bytes_generated": chunks * CANDIDATES_PER_CHUNK * word_bytes}
        raise ExpansionError("public row rejection budget exhausted; no fallback row emitted")

    def iter_rows(self, family, start, count, N, q):
        """Yield one list per row at indices start through start+count-1."""
        start = _integer(start, "start")
        count = _integer(count, "count")
        if start + count > U64_LIMIT:
            raise ValueError("row index range overflows 64 bits")
        # Validate the context even for an empty requested row sequence.
        self.row_domain(family, start, N, q)
        for index in range(start, start + count):
            yield self.row(family, index, N, q)
