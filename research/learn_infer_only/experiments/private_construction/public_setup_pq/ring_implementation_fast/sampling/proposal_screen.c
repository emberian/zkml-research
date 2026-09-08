/* [DERIVED] Integer-only sequential proposal screening. No RNG or file I/O. */
#include <stdint.h>
#include <stddef.h>

typedef struct {
    uint64_t offset, produced, proposals, squeeze_accepts, squeeze_rejects;
    uint64_t gray, boundaries, caps, attempt;
    int64_t pending_k;
    uint64_t pending_prefix;
} sampler_state;

static uint64_t read_le(const uint8_t *p, unsigned n) {
    uint64_t x = 0;
    for (unsigned j = 0; j < n; j++) x |= (uint64_t)p[j] << (8 * j);
    return x;
}

/* Return 1 at a pending gray proposal, 0 on buffer/output completion, -1 on
   invalid public arguments. Gray is already charged to attempt/proposals;
   the caller resolves it before resuming. All other candidates are consumed
   in order and cap fallback is applied before the next candidate. */
int screen(const uint8_t *bytes, uint64_t nproposals, unsigned a,
           const uint64_t *low, const uint64_t *high,
           int64_t *output, uint64_t count, sampler_state *s) {
    if (a > 59 || s->attempt >= 4096 || s->produced > count ||
        s->offset > nproposals) return -1;
    const unsigned proposal_bytes = (a + 11) / 8;
    const unsigned stride = proposal_bytes + 4;
    const uint64_t mask = (UINT64_C(1) << (a + 4)) - 1;
    const int64_t boundary = INT64_C(1) << (a + 3);
    while (s->offset < nproposals && s->produced < count) {
        const uint8_t *p = bytes + s->offset * stride;
        const int64_t k = (int64_t)(read_le(p, proposal_bytes) & mask) - boundary;
        const uint64_t prefix = read_le(p + proposal_bytes, 4);
        s->offset++; s->proposals++; s->attempt++;
        int accepted = 0;
        if (k == -boundary) {
            s->boundaries++;
        } else if (k == 0) {
            s->squeeze_accepts++;
            accepted = 1;
        } else {
            const uint64_t magnitude = (uint64_t)(k < 0 ? -k : k);
            const unsigned cell = (unsigned)(a >= 9 ? magnitude >> (a - 9)
                                                          : magnitude << (9 - a));
            if (prefix < low[cell]) {
                s->squeeze_accepts++;
                accepted = 1;
            } else if (prefix >= high[cell]) {
                s->squeeze_rejects++;
            } else {
                s->gray++;
                s->pending_k = k;
                s->pending_prefix = prefix;
                return 1;
            }
        }
        if (accepted) {
            output[s->produced++] = k;
            s->attempt = 0;
        } else if (s->attempt == 4096) {
            output[s->produced++] = 0;
            s->caps++;
            s->attempt = 0;
        }
    }
    return 0;
}
