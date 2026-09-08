# Public setup/PQ source and instrument log

[EXECUTED] Date 2026-09-08. Only source extraction, hashing and prose/mathematics
were performed. No crypto/runtime/attack experiment, disclosure/routing tool,
malformed-input work or previously stopped task was run. PDFs came only from
the local IACR mirror; none was downloaded. Source-pin commands and SHA256
hashes are in SOURCE_MANIFEST.json; output is pin_sources.stdout.json.

## Local primary-source access

[SOURCE] Mirror root: /Users/ember/dev/gh/forks/IACR-eprint-mirror/.
Page references below use each PDF's printed pagination. Extracts are local
working material, reproducible by the manifest's pdftotext commands.

| Source | Actual access and scope |
| --- | --- |
| [2015/608](https://eprint.iacr.org/2015/608), Agrawal–Libert–Stehlé | §4.1–4.2 algorithms/parameters; Theorems2–4 statements; §4.2 game/proof; Appendix C Lemmas6–10, especially p34 Lemma10; targeted conditional-distribution proof passages pp15–20. Numeric modular IPFE, prescribed τ and syndrome regularity. All reductions' QPT scope not fully audited. |
| [2021/046](https://eprint.iacr.org/2021/046), mirror 2021/46.pdf | §4 RLWE equations, §6 pp22–24, Appendix D.4 pp43–45. Local issuer master/masks in MIFE/MCFE/DMCFE and static/ROM scope. Prior executable audits not repeated. |
| [2023/395](https://eprint.iacr.org/2023/395), Registered (Inner-Product) Functional Encryption | Abstract, intro/contributions, theorem overview and basic registry syntax. Inner-product predicates/pairings versus numeric LWE IPFE; general-circuit iO path. |
| [2025/044](https://eprint.iacr.org/2025/044), Registered ABE and Adaptively-Secure Broadcast Encryption from Succinct LWE | Abstract, intro and selected setup/trapdoor algorithms, including Algorithm1 SuccinctTrapGen. Stronger succinct-LWE/ROM assumptions and structured setup; a public related trapdoor is not automatically an unrestricted reader. |
| [2024/1572](https://eprint.iacr.org/2024/1572), Bounded Collusion-Resistant Registered Functional Encryption for Circuits | Abstract/intro, §4.1 gsRBE setup and Theorem2, §4.3 overview, §5.1 compiler and remark. Q-bounded SIM RFE, LWE+evasive-LWE path, PKE CRS/dummy-key lifecycle. Lattice variant removes dummy-key step. |
| [2025/836](https://eprint.iacr.org/2025/836), Compact Registered Functional Encryption for Attribute-Weighted Sums with Access Control | Abstract and intro assumption/security overview. Numeric registered AWS exists; instantiations use bilateral k-Lin pairings. |
| [2025/967](https://eprint.iacr.org/2025/967), Registered Functional Encryption for Pseudorandom Functionalities from Lattices | Abstract and intro functionality/assumption overview. Pseudorandom functionality prerequisite; LWE plus evasive-LWE-based primitive. |
| [2025/1039](https://eprint.iacr.org/2025/1039), Unbounded Distributed Broadcast Encryption and Registered ABE from Succinct LWE | Abstract/intro, §3 overview, Construction4.2 and Remark4.13 p22; Definition5.1 pp23–24, Definition5.5 and Remark5.6 pp25–26; Construction5.11 pp32–34, Theorems5.13–5.14 and proof overview; Remark5.31 p51. Explicit transparent setup via decomposed LWE, independent user key/public aggregate, predicate semantics and ROM extraction scope. Full QROM/concrete NIZK public-coin audit not done. |

[EXECUTED correction] An initial attempt at 2021/046.pdf failed because the
existing mirror file is 2021/46.pdf. The corrected extraction used that local
file; its saved text is extracts/2021-046.txt. No missing PDF was fetched.

## Web discovery instrument

[EXECUTED] Eight search queries in batches of 3+3+2; Kagi0. Results were
checked against primary sources. This is a bounded instrument, not a corpus
exhaustiveness/absence claim.

1. "registered" "inner product" "LWE" encryption
2. "decentralized" "inner-product" "lattices" encryption
3. "functional encryption" "public" "Gaussian" "setup"
4. "registered" "functional encryption" LWE (eprint.iacr.org / iacr.org)
5. "Decentralized Multi-Authority" "Noisy and Evasive" (eprint.iacr.org / arxiv.org)
6. "Registered ABE" "succinct" LWE (eprint.iacr.org / iacr.org)
7. "Bounded Collusion-Resistant Registered Functional Encryption" eprint
8. "Registered Functional Encryption for Attribute-Weighted Sums" LWE eprint

[SOURCE] Primary metadata pages opened: IACR news items
[25923](https://www.iacr.org/news/item/25923) and
[25699](https://www.iacr.org/news/item/25699);
[David Wu's publication list](https://www.cs.utexas.edu/~dwu4/publications.html);
[Robert Schädlich's publication list](https://rschaedlich.github.io/) (twice);
the [2025/1039 landing page](https://eprint.iacr.org/2025/1039) via a successful
author-page link click; and [arXiv:2505.11744](https://arxiv.org/abs/2505.11744).
The Wu page also had two within-page finds. A preceding wrong-reference click
returned invalid argument and yielded no content. Total non-search navigation:
6 requested opens, 2 finds, 2 click attempts (1 successful). No PDF downloads.

[SOURCE, abstract only] Liu–Wang–Fu arXiv:2505.11744 reports noisy/evasive
multi-authority IPFE and an exact modulus-switching variant, with static ROM
security under LWE and new evasive-IPFE assumptions. A full local mirror copy
was not identified/read in this tranche. Its authority lifecycle is an open
source check, not evidence of absence. The 2025 user-specific pre-constraining
framework was identified by metadata only; it is not used as a proved premise.

## Scry instrument

[EXECUTED] Four SQL submissions: two distinct queries, each retried once after
query_capacity_exhausted at its 45-second admission deadline. Two completed
responses. Schema0; reused private_construction/sources/scry_schema_openalex.txt.
No additional SQL followed the successful retries.

    SELECT id,title,doi,primary_location.landing_page_url,publication_year
    FROM openalex.works
    WHERE hasAllTokens(search_text_lc,['registered','functional','encryption'])
    ORDER BY publication_year DESC,cited_by_count DESC LIMIT 20

[SOURCE] Initial error: searches/scry_1.json. Success: searches/scry_1_retry.json,
record 34753e16-31e1-41f4-aa19-cd2ed0825f24, 4 rows: registered AWS (2026),
user-specific pre-constraining framework (2025), bounded-collusion circuit RFE
(2024), registered IPFE (2023). Reported spend_nanodollars=0,
burden_nanodollars=2569028, billing free_slack.

    SELECT id,title,doi,primary_location.landing_page_url,publication_year
    FROM openalex.works
    WHERE hasAllTokens(search_text_lc,['decentralized','encryption','lattices'])
       OR hasAllTokens(search_text_lc,['decentralized','inner','lwe'])
    ORDER BY publication_year DESC,cited_by_count DESC LIMIT 15

[SOURCE] Initial error: searches/scry_2.json. Success: searches/scry_2_retry.json,
record 1c75f37f-b832-443d-bdee-a97434adfe34, 1 row: arXiv:2505.11744.
Reported spend_nanodollars=0, burden_nanodollars=407570, billing free_slack.
Errors did not report spend; no cost is invented for them. Successful results
report snapshot-based OpenAlex coverage, a publication-date maximum 2026-09-08,
and freshness lag about 6.41 million seconds. Dates are not a live corpus claim.
Complete returned coverage and metrics remain in the saved raw responses.

[DERIVED] The positive result in AUDIT.md is an explicit statistical setup
replacement from a read source lemma. Its PQ premise and semantic-image check
remain explicit; neither a search omission nor scalar-key count substitutes
for those arguments.
