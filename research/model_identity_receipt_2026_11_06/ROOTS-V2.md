# Registry v2 roots (mir13): normative

What a second implementation needs to reproduce the root set byte for byte. The reference implementation is
`stream/src/{conv,tree,main}.rs`; the conversion half is checked against FlashProve's exact-rational oracle
(`weight_sums/tests/oracle.py`) and, on Llama 4 Maverick, against the `wsums.txt` digest FlashProve published.

## 1. The object: FlashProve's committed integers

The committed object is the integer model FlashProve's `cp_commit` commits, not the GGUF bytes and not any float
checkpoint. FlashProve `docs/model.md` section 11 defines it: each committed tensor (section 11.3's table) is decoded
block by block in binary32 (11.2), multiplied by its norm's gain times a constant if it reads one, given one exponent
e per tensor (the largest with RNE(2^e max|p|) <= 4095; the embedding takes e_res), and rounded: w = RNE(2^e p).
Matrices are int16, the embedding int32, both little-endian two's complement. Elements are in file order: index
i0 + dims[0] (i1 + dims[1] i2); a **row** is one value of (i1, i2), dims[0] elements; a **slice** is one value of i2
(for `ffn_*_exps`, one routed expert), dims[1] rows.

Field reading: FlashProve computes in Goldilocks, p = 2^64 - 2^32 + 1. A matrix integer |w| <= 4095 and an embedding
integer |w| < 2^30 map injectively to w mod p, so the byte leaf below is a leaf of field elements under a fixed,
injective encoding.

## 2. The hash

H_k(X) = cSHAKE256(X, L = 256, N = "", S = "mir13/v2/" || k) (NIST SP 800-185), per the minidregg ruling
(`board/RULINGS.md`: cSHAKE256 for roots; open with a boolean proof over Keccak). Integers below are little-endian:
u32, u64, i32 as 4, 8, 4 bytes.

| name | definition |
|---|---|
| leaf(row) | H_leaf(the row's integers, 2 or 4 bytes each) |
| merkle(d_1..d_n) | n = 0: H_empty(""); else pad to the next power of two with H_pad(""), node(l, r) = H_node(l \|\| r), up to one root |
| slice root | H_slice(u64 rows \|\| u64 dims[0] \|\| merkle(leaves of the slice's rows)) |
| tensor root | H_tensor(u32 len(name) \|\| name \|\| u32 ndims \|\| u64 dims... \|\| i32 e \|\| u8 width (2 or 4) \|\| u64 slices \|\| merkle(slice roots)) |
| expert root R_{l,e} | H_expert(u32 l \|\| u32 e \|\| for gate, up, down of layer l: i32 exponent \|\| slice root e) |
| root set | H_rootset(u64 #tensors \|\| for each committed tensor by name as bytes: u32 len \|\| name \|\| tensor root \|\| u64 #experts \|\| for each (l, e) ascending: u32 l \|\| u32 e \|\| R_{l,e}) |

The exponent enters R_{l,e} because a row's value is w 2^-e; two experts with the same integers under different
exponents are different experts.

## 3. What binds what

- Row granularity: an opening of one row of one expert costs a Merkle path of log2(rows) nodes; a selected expert's
  R_{l,e} is found by the verifier from the public root vector (`notes/moe-router-binding.md` 5.3).
- The root set binds every committed tensor's integers, exponent, shape and name, and every routed expert's three
  matrices with its index. It does not bind the norms' gains separately (they are inside the products), the tokenizer,
  or anything section 11 does not commit; those are nodes of the receipt's provenance graph.
- Nothing in FlashProve opens these roots: FlashProve opens its own salted, randomised table. The roots' consumers
  are the receipt verifier (identity), a stranger's recomputation, and the house's expert-swap binding.
