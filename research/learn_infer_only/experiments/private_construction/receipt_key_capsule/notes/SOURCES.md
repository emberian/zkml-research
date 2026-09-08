# Capsule source access and query accounting

[EXECUTED, 2026-09-08] Scope: two-input FE release games and a bounded search
for restricted FE, lockable obfuscation and signature-triggered release. Primary
technical claims use the local papers below. Web snippets and OpenAlex rows
were discovery data only. No PDF was downloaded; all full-paper reading used
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/<year>/<id>.pdf`.
`SOURCE_MANIFEST.json` pins exact PDF/text bytes and extraction commands.

| Source | What was actually inspected | Main contribution to this audit |
|---|---|---|
| [SOURCE] [2013/727](https://eprint.iacr.org/2013/727), four-author precursor | Syntax/game pp.8–12; iO Theorem14 and H4/H5 reduction pp.17–18,30–31; Theorems15–17 pp.18,21; SIM implications pp.23–24. Printed page = PDF page minus1. | Public-slot exact compatibility; selective vs adaptive IND; SIM positive only with no exposed encryption slot; general SIM obstruction not a specific-family impossibility. |
| [SOURCE] [2024/740](https://eprint.iacr.org/2024/740), Nguyen–Phan–Pointcheval | Abstract/contribution pp.1,7–8; Definitions2–6 pp.14–16; constructive summary/Corollary13 p.25 located. PDF pages equal printed. Full pairing reduction not audited. | Public attributes are bound during ciphertext issuance; concrete IP+LSSS class; semantic admissibility remains. |
| [SOURCE] [2021/1324](https://eprint.iacr.org/2021/1324), Kluczniak | Introduction p.4; Definition5 pp.13–14; Theorem2 p.16 and opening simulation hybrids. PDF pages equal printed. Full construction/cycle-testing reduction not audited. | Later lockable construction retains distributional target requirement and fixed output message. |
| [SOURCE] [2025/045](https://eprint.iacr.org/2025/045), Chaturvedi et al. | Abstract p.1; positive construction Definition2/Theorem1 pp.23–24; AppendixB pp.28–29 input-specific GC/ABE lifecycle. PDF pages equal printed. No attack experiment executed or used as an experimental result. | `Dec` still takes raw secret; GC embedding needs a complete lifecycle to meet permanent public capsule exposure. |
| [SOURCE] [2024/1477](https://eprint.iacr.org/2024/1477), Avitabile et al., September20,2024 | Abstract and overview pp.1–5; SPS Definitions14–17 pp.11–12; cSWE Definitions19–22 pp.13–14; construction overview; Theorem3 and first punctured-key/exact-equivalence hybrids pp.17–19. PDF pages equal printed. Full later hybrid chain and TM iO instantiation not independently reproved. | A genuine selective signature-triggered fixed-message release theorem; strong puncturing turns nonavailability into nonexistence in its hybrid. |

[SOURCE: existing local audit] Before searching, read
`../../lockable_gate/README.md` and `SEARCHES.md`: original 2017/274,2017/276,
2019/1010 games, fixed-message issue and known-unlock prediction lemma. Those
PDFs were not re-extracted by this tranche. Also read `PRIVATE_CONSTRUCTION.md`,
`PRIVATE_INGRESS.md`, `PQ_COMPOSITION.md`, current STATUS/NEXT, handoff then
companion, overnight brief, repository laws and source-lane brief. Historical
PQ interface first-pass statements are superseded by their recorded reviews;
none supplies this capsule's missing source game.

[EXECUTED corpus/instrument qualification] Relevant old notes were discovered
with repository `rg` and read directly, excluding safety-stopped task paths.
The evidence for the scoped conclusion is these five local PDFs plus the prior
lockable audit. No statement here asserts absence from cryptography as a field.

## New metered calls

[EXECUTED] **SQL2, schema0, Kagi0.** Reused the existing OpenAlex schema at
`../../sources/scry_schema_openalex.txt`. Helper `swarm/tools/scry.py` used
`SCRY_MAX_SECONDS=45` and read the configured credential internally without
printing it. Both calls completed, no retry. Saved records each report
`billing_mode=free_slack` and `spend_nanodollars=0`; burden counters are recorded
separately by Scry and are not user spend. No total-system spend is inferred.

[EXECUTED SQL1] `../searches/scry_1.json`, record
`0177dbb7-77f1-4623-aaac-27b5f9d6b42a`: eight metadata rows, mostly irrelevant
resource-constrained HE papers. This query did not locate the new MCFE paper;
web discovery did. That demonstrates a coverage/indexing limitation of this
particular query, not a field absence.

```sql
SELECT id,title,doi,primary_location.landing_page_url,publication_year
FROM openalex.works
WHERE hasAllTokens(search_text_lc,['functional','encryption','public','inputs'])
   OR hasAllTokens(search_text_lc,['constrained','homomorphic','encryption'])
ORDER BY publication_year DESC,cited_by_count DESC LIMIT 18
```

[EXECUTED SQL2] `../searches/scry_2.json`, record
`40b40039-107c-434c-83a9-c6980d74aa6e`: ten rows, including SWE compact
ciphertext and the circular-insecure-FHE lockable paper. This is metadata
rather than an audited theorem. Later repository-upload dates in metadata do
not change the publication/version dates printed in the mirrored papers.

```sql
SELECT id,title,doi,primary_location.landing_page_url,publication_year
FROM openalex.works
WHERE hasAllTokens(search_text_lc,['lockable','obfuscation'])
   OR hasAllTokens(search_text_lc,['witness','encryption','signature'])
ORDER BY publication_year DESC,cited_by_count DESC LIMIT 18
```

## New web calls

[EXECUTED] **Eight search queries** in three tool batches (3+3+2), with no
retries. Results found primary paper IDs/author or institutional pages; claims
were checked at local full source. Several broad queries returned little useful
material and non-primary relays; those relays were not used as evidence.

1. `"functional encryption" "constrained" "FHE" proof decryption`
2. `"multi-input functional encryption" "computational" "compatibility"`
3. `"lockable obfuscation" "auxiliary" signatures`
4. `"Multi-Client Functional Encryption with Public Inputs and Strong Security"`
5. `"constrained fully homomorphic encryption" decryption`
6. `"functional encryption" "signature-protected" OR "policy-restricted" OR "authenticated" release`
7. `"constrained FHE" cryptography`
8. `"constrained fully" "homomorphic" encryption cryptography release`

[EXECUTED] Three separate web page-open attempts failed with a non-retryable
safe-open error: Figshare article32771082, its public API metadata endpoint,
and DOI `10.1007/978-981-96-0875-1_1`. A normal Python `urllib` GET of the public
API metadata succeeded; saved as `../searches/figshare_32771082.json`. This was
a public metadata fallback, not a PDF request. Its file list identifies
`2024-1477.pdf`; that ID was then read exclusively from the local mirror.
The [CISPA publication record](https://publications.cispa.de/articles/conference_contribution/Signature-based_Witness_Encryption_with_Compact_Ciphertext/32771082)
is the primary institutional record linked by that metadata. Its abstract is
not substituted for the source game.

[EXECUTED exact metadata command] The retained response was obtained with
`urllib.request.urlopen('https://api.figshare.com/v2/articles/32771082', timeout=20)`
and written directly to the named public JSON artifact. Zero eprint landing
page opens; zero network PDF downloads. Indexed PDF snippets returned by web
search are counted as search results, not local full-source reads.

[OPEN] No source-backed instantiated PQ capsule, adaptive-tag cSWE theorem,
concrete cryptographic cost estimate, or end-to-end learner construction is
claimed. The remaining game/algorithm obligations are in `AUDIT.md` §4–6.
