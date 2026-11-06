# Redesign lane: grounding (what was read, what each source fixes, where sources disagree)

2026-11-06. Question (ember): given what we learned about the hardware today, is there a proof-system design with
higher total-system composed performance? Tags: [READ] seen at file:line or section; [MEASURED] run here or by a
sibling lane (run id given); [MODEL] a predicted bound; [A] assumption.

## 1. Facts this lane builds on

| fact | value | source |
|---|---|---|
| The leaf workload is byte- and bit-shaped relations over cSHAKE-committed content | DFA/complement, CFG replay, MMR non-omission, audit receipts | [READ] docs/LEAF-PROVER-DECISION.md section 0 |
| Store roots are cSHAKE256 by ruling; "to make openings faster, change the proof system, not the root hash" | BLAKE3 only where an outside format fixes it | [READ] minidregg board/RULINGS.md (Hashes bullet) |
| Today's leaf commits ONE symbol per 32-byte Tower256 element, one element per Merkle leaf | ell 14 = 4 KiB record; 65,493 Keccak-f per column tree, "about 2,100x the 31 Keccak-f of the record's own cSHAKE content root" | [READ] minidregg docs/TOWER256-FRI-PROVER-WORK.md section 2 (branch lane/tower256-prover-exe 6fd5d4f63) |
| A certificate trace has several columns; per-column trees multiply the Merkle term | byte, state, position, multiplicity | [READ] same, section 3 |
| CPU prover (fixed, PCLMUL) is Merkle-bound | 55 ms per proof at ell 14, 78% Merkle; Keccak-f 536 ns, Tower256 mult 22.9 ns on a Kaggle Xeon core | [MEASURED] accelerator-readiness/TOWER256.md section 3, accel-tower-dryrun-04 |
| GPU prover (T4) is arithmetic-bound | encode 80% of device time at ell 20; table mult 12,000-17,400 int32-op equivalents; bit-sliced 52,700 | [MEASURED] TOWER256.md sections 4, 8 |
| A single proof does not need a GPU; batches do | 0.82 ms per ell-14 word in a 64-word batch, about 57 Xeon cores | [MEASURED] TOWER256.md section 4 |
| Measured T4 wall is dominated by the Python host's openings | 223 of 362 ms at ell 20 | [MEASURED] accel-tower-dryrun-04 (Codex pointed this out, CODEX.md) |
| Tensor GF(2) fixed-r route: modelled 2.3-3.2x per proof (5.3x with tensor fine layers); **unfused T4 measurement loses**: 22.6 ns/element INT8 against 2.9-4.3 ns for the table | | [MODEL] ROTATION.md 2(b),(c); [MEASURED] MMA.md section 9 |
| Subfield twiddles shrink a fixed multiply 8x (GF(2^32)) or 16x (GF(2^16)) | "a statement-design lever" | [READ] F3-MODEL.md item 6; ROTATION.md 2(b) |
| Keccak has no tensor form; SIMT Keccak gains only SMs x clock across generations | T4 -> B300 6.5x | [READ] OPTIMAL.md Rule 2, ROTATION 2(c) |
| Prime-field primitives are HBM-bound on every target with a tensor path | 1.2-1.6x copy on T4 | [MEASURED] OPTIMAL.md Rule 1, ROTATION 2(a) |
| Binary recursion cost per hash | Keccak-f 38,400 constraints; BLAKE3 14,000; SHA-256 30,376; BinarySpartan 287k Keccak-f/s on 12 M4 Max cores | [X] ePrint 2026/1656 section 4, quoted in PROOF-SYSTEM-SPACE section 0 and by Codex |
| BabyBear Keccak-f | 63,192 committed cells per permutation | [READ] LEAF-PROVER-DECISION section 1 |
| UD-100 at rate 1/4 | 148 queries; verifier 53,263 Keccak-f at ell 14 | [READ] TOWER256-FRI-PROVER-WORK section 2 |
| Lean assets for the binary path | Tower256 coordinate arithmetic proved equal to the field; cSHAKE256 proved equal to spec; raw/succinct additive-FRI controllers with collision extraction; RS MCA over the whole UD radius via the ArkLib bridge; `gf2_dot_*`, `lazy_bilinear` | [READ] LEAF-PROVER-DECISION section 6; ROTATION.md section 2(b) |
| ArkLib proves Binary BaseFold with ring switching | | [READ] PROOF-SYSTEM-SPACE section 0 item 6 |
| Dark learning: 61-bit prime spine/middle; the ZKPoPK is Ligero over a 255-bit field; 0.5-1.4 Gbit per step; Python prover 417-606 s per batch | | [READ] DARK-LEARNING-SCHEME-DECISION section 20 |
| TPU: no 64-bit in Pallas, VPU peak unpublished, long VPU chains spill through HBM in XLA | | [READ] tpu-perf/GROUNDING.md, STYLE.md |

## 2. Where the sources disagree (and which this lane uses)

- **Bit-sliced Tower256 multiply cost.** OPTIMAL.md 3.2 (hw-optimality, same day) still uses ~700 ops [A] and calls
  bit slicing the predicted optimum. TOWER256.md section 8 measured 52,700 and showed 718 is below the ideal
  instruction count (860). This lane uses the measurement. OPTIMAL.md's 3.2 bound for the encode is therefore
  optimistic by ~20x for 256-bit general multiplies; it is roughly right for 16-bit subfield multiplies (16 planes fit
  in registers), which is the case this lane's design uses.
- **Tensor GF(2) speedup.** ROTATION models 2.3-3.2x per proof (fused, unbuilt); MMA.md section 9 measured the unfused
  T4 kernel at 5-8x slower than the table. Both are reported; the model's design (b) is tagged [MODEL, fused].
- **BLAKE3 constraint count.** 14,000 per compression is quoted from 2026/1656; Codex notes repository summaries with
  conflicting throughput figures. This lane uses the structural constraint counts only.

## 3. Not read (by rule or scope)

/Users/ember/dev/nanodregg and /Users/ember/hellas (rule). breadstuffs automata chapters beyond COUNTS.md section 4.
The paid B200 run (accel-b200-mma-01) was in flight when this lane wrote its model; its results are not used.
