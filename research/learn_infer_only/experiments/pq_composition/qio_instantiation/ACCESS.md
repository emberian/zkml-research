# Source-access record

[EXECUTED provenance] `audit.py` extracts and runs `pdfinfo` on six local mirror PDFs, recording commands, stdout/stderr, return codes, PDF/extract hashes and locator pages in `audit.json`. PDF-page numbers equal printed numbers for the passages used here. Extracts and renders are ignored. Source access is bounded as follows; extracting a PDF does not imply reading every page.

| Source | Access in this tranche |
|---|---|
| [SOURCE] 2025/2215 | Re-read Theorem 2 p.3; SMS/iO definitions and parameter/correctness statements pp.9–11; Definition 6 p.16; complete main construction, correctness, precondition/postcondition proof and efficiency pp.17–21; Appendix A pp.25–26; read optional Appendix B's primitive list and proof sketch pp.26–28 to identify why its efficiency transformation is not free. No PROM theorem used. |
| [SOURCE] 2025/096 | Efficiency/LWE convention p.12; succinct-NIVOLE dependency p.15; SMS algorithm/security parameter passages pp.16–21, especially the Alice-encoding security interface. The Bob-simulation hybrids were previously read in the initial source lane. This tranche does not reprove the referenced lattice reductions. |
| [SOURCE] 2016/006 | Classical/nonuniform conventions p.4; primitive/subexponential definitions and inherited Theorems 3–5 pp.5–7; complete Theorem 6 construction and reduction pp.9–11; Theorem 7 p.11. |
| [SOURCE] 2015/720 | Concrete indistinguishability/subexponential conventions §2; Theorems 11–12 and their constructions/simulators/hybrids pp.30–34; Corollary 3 and Theorem 13's bounded circuit construction and proof sketch pp.35–36; Theorem 15 p.37. Read the child-coin/child-encoding switches in §4.1 pp.21–23 for the step referenced by the bounded proof, without claiming the separate unbounded-input theorem. |
| [SOURCE] 2012/733 | FE/ABE/FHE/garbling theorem interfaces and FE security timing pp.12–22; simulator and complete FE hybrid reductions pp.25–29, including how the adversary state is forwarded. No recursive audit of the cited lattice ABE/FHE or Yao base proofs. |
| [SOURCE] 2014/917 | §4 pp.12–14, shallow-function FE bootstrap algorithms, Theorem 3 hypotheses and complete printed hybrid sketch; noted the private-key direct construction and asserted public-key counterpart. No adaptive-security compiler claim used. |

[EXECUTED visual checks] Both commands below exited 0 with empty stdout/stderr. Both resulting PNGs were inspected using `view_image`, confirming the SMS error exponent, all-input correctness definition and xiO-bootstrap error factor.

```sh
pdftoppm -f 10 -l 10 -scale-to 1700 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/2215.pdf research/learn_infer_only/experiments/pq_composition/qio_instantiation/renders/2025-2215-p10
pdftoppm -f 11 -l 11 -scale-to 1700 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/2215.pdf research/learn_infer_only/experiments/pq_composition/qio_instantiation/renders/2025-2215-p11
```

[EXECUTED network accounting] Two web metadata searches were issued, in one call:

1. `"Output-Compressing Randomized Encodings and Applications" eprint`
2. `"Reusable Garbled Circuits and Succinct Functional Encryption" eprint`

[SOURCE discovery-only] Search results identified the local IDs 2015/720 and 2012/733, which were then verified from their local PDF contents. Third-party metadata and indexed PDF snippets were not substituted for theorem reads. There were no web opens and no PDF downloads. No Scry/schema/Kagi queries or new credentials were used.

[EXECUTED accounting] Six local PDFs; twelve successful extraction/metadata subprocesses; two successful visual-render commands. Ownership remained inside `experiments/pq_composition/qio_instantiation/`. No commits, companion edits, shared-ledger edits or frozen-proof changes.
