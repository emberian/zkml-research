# Sources and search accounting

[SOURCE: primary, theorem/proof read] Mark Zhandry, **Secure Identity-Based
Encryption in the Quantum Random Oracle Model**, eprint 2012/076.
Local PDF: `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2012/076.pdf`.
`extracts/2012-076.txt:250`, Theorem 3.1, PDF p.6: quantum-query output
statistics depend on 2q-point oracle marginals. `:630`, Theorem 6.1 and
Section 6, PDF p.13: efficient oracle-free simulation via finite independence
and a finite-field/Vandermonde construction.
[Primary landing page](https://eprint.iacr.org/2012/076).

[SOURCE: primary, stated fact read] Mark Zhandry, **How to Construct Quantum
Random Functions**, eprint 2012/182. Local PDF:
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2012/182.pdf`.
`extracts/2012-182.txt:194`, Fact 2, PDF p.5, restates exact 2q-wise simulation
and attributes it to the earlier work. Used as corroboration, not a
replacement for the original theorem/proof.
[Primary landing page](https://eprint.iacr.org/2012/182).

[SOURCE: primary, theorem and full density-matrix proof read] Dan Boneh and
Mark Zhandry, **Quantum-Secure Message Authentication Codes**, eprint
2012/606. Local PDF:
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2012/606.pdf`.
`extracts/2012-606.txt:1260`, Lemma 6.4, PDF pp.23–24: c classical and q
quantum queries require c+2q independence; the proof compares final density
matrices. [Primary landing page](https://eprint.iacr.org/2012/606).

[SOURCE: supplied primary extract, scoped sections read] Grilo, Hövelmanns,
Hülsing and Majenz, **Tight adaptive reprogramming in the QROM**, eprint
2020/1361. Parent extract `../extracts/2020-1361.txt`: Proposition 1 at
line 316; Theorem 1 at line 374; Appendix A starts at line 1754, including
its overriding-list simulation. Finite output sets and uniform refreshed
values are explicit source conditions. Parent owns the full block-reprogramming
application. [Primary landing page](https://eprint.iacr.org/2020/1361).

[EXECUTED extraction] For each id in {076,182,606}, executed
`pdftotext -layout /Users/ember/dev/gh/forks/IACR-eprint-mirror/2012/<id>.pdf`
with output `extracts/2012-<id>.txt` in this directory. All three exited 0
with empty stdout. Full local extracts and their hashes are retained. No
PDF was downloaded from eprint or another website.

[EXECUTED web search count: 2] The exact discovery queries were:

1. `Zhandry "2q-wise" "random functions" theorem`
2. `site.markzhandry.com OR site.m.zhandry.org OR site.iacr.org "Secure Identity-Based Encryption" "2012" Zhandry`

[SOURCE scope] Search results identified the primary eprint records and
author publication page. Nonprimary mirrors/search snippets were discovery
leads only. The claims above rely on the local primary PDFs actually read.
No further web queries were issued; the parent separately tracks its own
two searches. Query strings and this file retain the instrument/corpus scope.
