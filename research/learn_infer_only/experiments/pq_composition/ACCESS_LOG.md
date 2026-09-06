# Source access and resumption record

[EXECUTED] Dedicated source lane started 2026-09-06 at 09:25 UTC. Ownership is this directory and `../../PQ_COMPOSITION.md`. Shared ledgers, companion trees and `docs/VERDICTS.md` were read only. No commits or external messages were made. Agent coordination stayed within the research swarm.

[EXECUTED] `python3 research/learn_infer_only/experiments/pq_composition/source_audit.py > research/learn_infer_only/experiments/pq_composition/source_audit.stdout.txt` regenerates `source_manifest.json`. It records exact `pdftotext -layout` and `pdfinfo` commands, return codes, stdout/stderr, local PDF/extract hashes, locator pages and literal token counts. Extracts and rendered pages are ignored. No PDF was fetched from the network.

[SOURCE: access levels] All seven PDFs were extracted locally; extraction does not mean every page was read. The audited passages are:

| Source | Actually read |
|---|---|
| [SOURCE] 2025/2215 | Introduction/Theorems 1-2 pp.1-4; SMS and obfuscation definitions pp.8-11; aviO Definition 6 p.16; complete standard-model construction/correctness/security/efficiency §§6.1-6.4 pp.17-21; equivocal-hash and decomposable-decryption appendices pp.25-26. The PROM construction/reduction beyond its definition was not audited. |
| [SOURCE] 2013/729 | IND games and implications pp.7-9; primitives pp.10-12; construction pp.12-14; simulator and complete hybrid list pp.14-17; Appendix A security reductions pp.19-24; Appendix B correctness and Appendix C SIM-to-IND pp.24-25. |
| [SOURCE] 2025/330 | Introduction pp.7-8; PKE/iO definitions p.18; compatibility Definition 4.3 p.22 (timing and quantitative obstruction already audited by the private-construction lane); §6.1 parameters p.48; Construction 2 pp.48-49; Theorem 6.1 p.50; hybrid proofs Lemmas 6.2-6.8 pp.64-67. Not every intervening hybrid-program listing was re-audited. |
| [SOURCE] 2016/006 | Main theorem p.2; classical PPT/nonuniform notation p.4; Theorem 6 construction and hybrid proof pp.9-11; bootstrapping Theorem 7 p.11. Referenced FE-to-iO transformations were not recursively audited. |
| [SOURCE] 2013/650 | Weak-extractability Definition 6.1 and Theorem 6.2, extractor and proof, printed pp.31-36 / PDF pp.32-37. |
| [SOURCE] 2015/1113 | Classical subexponential iO definition PDF pp.6-7; weak-extractability Definition 3 and Theorem 1 PDF p.8; extraction-based MIFE reduction PDF pp.17-18; Appendix A and Figure 8 PDF pp.21-23. This PDF omits printed page numbers on those pages, so use PDF page numbers. |
| [SOURCE] 2025/096 | SMS Definition 4 PDF pp.13-14; LWE encoding/decoding construction and correctness/security discussion PDF pp.17-22. The purpose was to verify the SMS dependency and its modulus/noise and adversary model, not reprove every cited lattice lemma. |

[EXECUTED visual formula checks] These commands returned exit code 0 with empty output. Their PNGs were visually inspected with `view_image`:

```sh
pdftoppm -f 16 -l 16 -scale-to 1800 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/2215.pdf research/learn_infer_only/experiments/pq_composition/renders/2025-2215-p16
pdftoppm -f 8 -l 8 -scale-to 1800 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/1113.pdf research/learn_infer_only/experiments/pq_composition/renders/2015-1113-p08
pdftoppm -f 22 -l 22 -scale-to 1800 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/1113.pdf research/learn_infer_only/experiments/pq_composition/renders/2015-1113-p22
```

[SOURCE: visual reads] The first image confirms PPT `KeySamp`/`Sim`, classical keyed circuits and equations (5.1)-(5.2). The second confirms `delta`, the rescaled iO parameter `k^(1/alpha)`, perfect correctness and the inverse-gap extractor bound. The third confirms repeated use of the same `z` and the inner-loop count `t=k/epsilon^2`; the text extraction drops several minus signs and Greek letters in this paper, so the images govern those formulas.

[EXECUTED web accounting] Four search queries and three opened HTML landing pages, across three `web.run` calls. Search queries were exactly:

1. `"On extractability obfuscation" eprint`
2. `"Indistinguishability obfuscation with non-trivial efficiency" eprint`
3. `"Simultaneous-message and succinct secure computation" eprint`
4. `"Multi-input functional encryption with" "Goyal" "Jain" "Neill" eprint`

[SOURCE: metadata reads] Opened HTML landing pages were `https://eprint.iacr.org/2025/2215`, `https://eprint.iacr.org/2013/729`, and `https://eprint.iacr.org/2025/330`. They reported revisions 2026-05-28, 2014-10-29, and 2025-12-06 respectively. Local PDF hashes, rather than an assumption that mirror dates match live metadata, pin all theorem claims. Search results included indexed PDF snippets; those were used only to identify local mirror IDs, never to replace local proof reads.

[EXECUTED accounting] Scry SQL 0; Scry schema 0; Kagi 0; new credentials used 0; new software installs 0; network PDF downloads 0. No literature-absence claim follows from these searches.

[OPEN next] Resume with the first unmet premises in `../../PQ_COMPOSITION.md`: specify quantum auxiliary-state and classical-interface games; then either audit the 2013 primitive suite and adapt correctness with an explicit error ledger, or supply a quantum weak-extraction theorem before reusing the newer route. Do not rederive the finite ladder here.
