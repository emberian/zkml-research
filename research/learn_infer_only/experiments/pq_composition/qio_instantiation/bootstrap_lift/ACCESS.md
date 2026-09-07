# Bounded source and execution record

[SOURCE / access] All primary PDFs were read from the local mirror, not downloaded. PDF text extraction is an access instrument, not a claim that every page was read. Printed/PDF page locations agree for the listed passages.

| Primary source | Exact access supporting this tranche |
|---|---|
| [SOURCE] 2016/006 | Definitions 3–5 pp.5–6; complete Theorem 6 construction and position-by-position hybrid reduction pp.9–11; Theorem 7 dependency chain p.11. Rechecked the distinction between output-position bound and maximum circuit-size bound. |
| [SOURCE] 2015/720 | Concrete security/PRG conventions §2 pp.7–8; the child-coin switch in §4.1 pp.22–23; PRG efficiency qualification §5 p.25; RE setup/simulation/efficiency Definitions 20–25 pp.28–30; complete Theorem 11 composition and Theorem 12 FE-to-RE construction/simulator/hybrids pp.30–34; footnote 8 p.32; bounded circuit algorithm and induction in Theorem 13 pp.35–36; Theorem 15 circuit consequence p.37. The separate unbounded-input/TM reductions are not claimed. |
| [SOURCE] 2015/173 | Appendix C pp.56–57 only, identifying the base-FE chain (IND-to-SIM, bounded-key amplification, depth bootstrap). This is a dependency locator, not a proof of those subtransformations. |
| [SOURCE / inherited] 2025/2215 | Main aviO-to-xiO algorithm/promise/correctness audit is the separately frozen predecessor `../INSTANTIATION.md`; no new interpretation of its LWE assumptions is claimed here. Its source hashes and exact access remain in `../audit.json` and `../ACCESS.md`. |

[EXECUTED command record] The following commands retain their output in this directory. `audit.py` records all six local PDF extraction/metadata subprocess commands, stdout/stderr, exit codes, PDF/extract hashes and locator-page checks in `audit.json`.

```sh
python3 research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/controls.py > research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/controls.stdout.txt
python3 research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/audit.py > research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/audit.stdout.txt
```

[EXECUTED scope] The controls check finite function compatibility, exact loss coefficients, a common-time-bound inequality and an all-node/path implication. Their toy functions are not FE/PRG instantiations. The bad-range countercontrol deliberately fails PRG security and only rejects a proof step that omits the PRG error term. No cryptographic security is established by executing these controls.

[EXECUTED query accounting] This tranche uses zero SQL, zero schema, zero web-search/open and zero Kagi queries; zero PDF downloads and zero installs. Local extracts/renders/vendors are ignored by this directory's `.gitignore`. Ownership is limited to `bootstrap_lift/`; no frozen-note, shared-ledger or companion edits and no commits.

[EXECUTED locator correction] The first audit invocation exited 1 because its provisional 2015/173 Appendix C locator string, `C     Proof of Theorem 6`, was absent. `rg` located the actual heading at extract line 3104: `C      From Compact (1)-Secure FE to Compact (qkey )-secure FE`. The script now checks the stable heading substring. This was a source-locator correction, not a failed theorem or a changed source PDF.

[EXECUTED link-parser correction] The second invocation exited 1 because the simple link regex treated code expressions ending in `](i)` and `](x)` as Markdown links. The checker now removes fenced and inline code before checking prose links. A following attempt to print the not-yet-created audit manifest consequently reported `FileNotFoundError`; the final successful run below supersedes those provisional checks.

[EXECUTED final source/control run] After those two instrumentation corrections, `controls.py` and `audit.py` both exited 0. The final manifest pins the bootstrap draft at `ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792` and the frozen predecessor at unchanged `163ebdcc5e376441b4a146b6964aba60002c3c55952cfb1e17d0c363478109fd`. `git check-ignore research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/extracts/2015-173.txt` exited 0 and returned that path, confirming the local extract is ignored.

[EXECUTED pointwise-correctness supplement] The following command exited 0 and retained 17,408 coefficient checks. It pins `POINTWISE_CORRECTNESS.md` at `c63e299a31a33617888814d5b4f371cf0f1e25541b4ebaa061e9bc84340d81f2` and asserts the frozen bootstrap hash remains unchanged. No new source or network queries were used for this derived supplement.

```sh
python3 research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/pointwise_controls.py > research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/pointwise_controls.stdout.txt
```

[SOURCE / read-only follow-up] After receiving the complementary base audit, the author spot-checked GKP 2012/733 §3.1 printed/PDF pp.23–24 and GVW 2013/337 §6.1 printed pp.15–16 (PDF pp.16–17) through the base lane's existing local extracts. These checks concern only setup/public-key/input-width formulas. No new extraction was performed and no source file was edited. Their source/extract hashes, exact pages and the original extraction-manifest hash are retained by `source_spotcheck.py`/`source_spotcheck.json`; this adds two read-only source accesses to the three PDFs in `audit.json`, with zero additional network queries.

```sh
python3 research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/source_spotcheck.py > research/learn_infer_only/experiments/pq_composition/qio_instantiation/bootstrap_lift/source_spotcheck.stdout.txt
```
