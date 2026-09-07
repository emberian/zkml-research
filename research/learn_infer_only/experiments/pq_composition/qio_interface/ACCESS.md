# Access record for the qualified-QIO interface lemma

[SOURCE access] Read local 2023/265 first-page title/authors, §4.1 p.19 quantum-adversary convention, Definition 4.3 p.20 and surrounding text, and Definitions 4.6–4.7 with the auxiliary/advice discussion pp.21–22. The local title is *Software with Certified Deletion*. The work was located through indexed references under the older title *Obfuscation and Outsourced Computation with Certified Deletion*. Local bytes govern all definition numbers and claims. No certified-deletion construction theorem is used.

[SOURCE access] Re-read local 2025/2215 Theorem 2 p.3, Definition 3 p.10, Definition 6 p.16 and the surrounding remarks. The earlier lane already read its main construction/reduction pp.17–21. This tranche does not re-audit the inherited xiO bootstrap or claim its quantum-advice security.

[EXECUTED extraction] `audit.py` records exact `pdftotext -layout` and `pdfinfo` commands, exit codes, stdout/stderr, hashes and PDF-page locators in `audit.json`. Its two PDF inputs are local mirror files. No PDF was downloaded.

[EXECUTED visual checks] The following two commands exited 0 with empty stdout/stderr. Both PNGs were opened using `view_image`. The images confirm the advice convention and all-sequences quantifiers in the local PDF; these are not abstract-only reads.

```sh
pdftoppm -f 19 -l 19 -scale-to 1800 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2023/265.pdf research/learn_infer_only/experiments/pq_composition/qio_interface/renders/2023-265-p19
pdftoppm -f 20 -l 20 -scale-to 1800 -singlefile -png /Users/ember/dev/gh/forks/IACR-eprint-mirror/2023/265.pdf research/learn_infer_only/experiments/pq_composition/qio_interface/renders/2023-265-p20
```

[EXECUTED search accounting] Three web search queries were issued:

1. `"indistinguishability obfuscation" "quantum advice" definition`
2. `"post-quantum" "obfuscation" "auxiliary" "non-uniform" definition`
3. `"Obfuscation and Outsourced Computation with Certified Deletion" eprint`

[SOURCE web access] Search snippets located the older 2023/265 title and a matching iO definition. An official Dagstuhl HTML page for *From Worst-Case Hardness of NP to Quantum Cryptography via Quantum Indistinguishability Obfuscation* was opened once at `https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.143/LIPIcs.ICALP.2026.143.html`; it was not used as theorem evidence, and no further source chase followed after the local 2023/265 definition was found. Indexed PDF snippets were discovery aids, not substitutes for local proof/definition reads.

[EXECUTED totals] SQL 0; schema 0; Kagi 0; web searches 3; HTML opens 1; network PDF downloads 0; new software installs 0. No corpus-wide absence claim is made.
