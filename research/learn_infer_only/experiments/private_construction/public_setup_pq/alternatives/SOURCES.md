# Sources and bounded search ledger

[EXECUTED, 2026-09-08] Initial source discovery used 6 targeted primary web
search queries and 4 Scry SQL submissions: 2 successful, 2 capacity errors.
No retries or extension-budget queries were used. Successful SQL responses
reported spend_nanodollars=0. No ePrint PDF was downloaded. All PDF content
was extracted from the absolute local mirror; the mirror stayed read-only.

## Primary constructions inspected

| [SOURCE] primary source | exact material inspected | use |
|---|---|---|
| Han, Yi, Liu, Gu, [2025/1613](https://eprint.iacr.org/2025/1613), *Tightly Secure Inner-Product Functional Encryption Revisited: Compact, Lattice-based, and More* | local complete extract; Def.1/2 and Fig.1 pp17–18; Fig.4–6 and Theorems2–4 pp25–28; Corollary1/Table2 p29; Gaussian smoothing Lemma15 pp76–77; visually rendered full pp28–29 | actual algorithms, key distribution, exposure game, decoder and finite source-premise check |
| Abdalla, Bourse, De Caro, Pointcheval, [2015/017](https://eprint.iacr.org/2015/017), *Simple Functional Encryption Schemes for Inner Products* | local title/version October1,2015; Construction4.1 pp9–10; §6 pp21–27, Regev algorithms and reproduction hypotheses | compact primal ciphertext; precise honest-key-image obstruction |
| Roy, Dutta, [2025/2232](https://eprint.iacr.org/2025/2232), *Toward Practical Lattice-based Unbounded Inner Product Functional Encryption: Construction and Implementation* | local Algorithms5–8 pp18–20 and23–26 pp28–29; Table2/Theorem9 p30; n=5 timing caption p8 | exact trapdoor/full-Z lifecycle and correlated hashed-coordinate keys; triage only |

[SOURCE metadata only] The [Springer chapter landing page](https://link.springer.com/chapter/10.1007/978-3-032-01881-6_6)
confirmed HYL authors, title and CRYPTO2025 publication. Its abstract supplied
no algorithm evidence. [IACR news item27277](https://iacr.org/news/item/27277)
resolved Roy–Dutta's ePrint identifier through its HTML link. Its timing/security
claims were not treated as reproduced results.

## Reused primary mathematics and fixture

[SOURCE] Micciancio–Peikert [2011/501](https://eprint.iacr.org/2011/501),
*Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller*, Lemmas2.3–2.4
pp12–13, equation(2.1); Gentry–Peikert–Vaikuntanathan
[2007/432](https://eprint.iacr.org/2007/432), *How to Use a Short Basis*,
Def.2.5/Cor.2.8 pp10–11 and Lemma5.2 p18. These were independently read in
the preceding finite-regularity lane. Here their general expectation formula
is used via the exact frozen BOUND.md, with an explicit new prime-modulus
substitution; the sufficient short-width/large-height corollary is not used.

[SOURCE] Agrawal–Libert–Stehlé [2015/608](https://eprint.iacr.org/2015/608),
§4.2 pp17–18 and Lemmas3–5 pp21–22, supplies the prior comparison only.
Its fixed-policy cost row and exact public fixture are pinned in the manifest.
No new claim relies on its printed Gaussian-conversion recipe, currently under
separate review. The original public policy file is
designated_span/crypto/rows.json; only public aggregate fixture facts are reused.

## Web search instrument

[EXECUTED] Two batches of three search queries, restricted to the primary
domains eprint.iacr.org and iacr.org:

1. `"inner product" "functional encryption" "compact" "LWE"`
2. `"inner product" "functional encryption" "noise flooding" LWE`
3. `"inner product" "functional encryption" "matrix" "lattice" compact`
4. `"inner-product functional encryption" "module" LWE`
5. `"inner-product functional encryption" "practical" lattices`
6. `"compact" "inner-product encryption" LWE numeric`

[EXECUTED] The web tool reported domain robots limitations but returned
indexed primary snippets. Metadata opens/clicks were separately used to
resolve exact papers. Failed opens included the DOI redirect, an initial
IACR news click, the www news-item variant, and CRYPTO2025 accepted/program
pages. Two direct HTML attempts returned403 (IACR index/accepted page).
A speculative CryptoDB identifier resolved an unrelated secret-sharing
paper and was discarded. These errors contributed no construction evidence.

[EXECUTED] Because the compact title had no resolved ePrint identifier,
the local-only title instrument ran `pdftotext -f 1 -l 1` on all 2,302 PDFs
under mirror/2025, normalized whitespace, and matched the exact substring
`Tightly Secure Inner-Product Functional Encryption`. Its single match was
2025/1613. `searches/local_title_scan.json` preserves count and matched page.
An earlier binary-text rg over those PDFs found no match; compressed PDF
bytes are not a content-absence instrument. No full-mirror absence is claimed.

## Scry submissions

[EXECUTED] All submissions used `SCRY_MAX_SECONDS=45 python3 swarm/tools/scry.py
sql '<query>'` and retained stdout under searches/. Existing local OpenAlex
schema was read before the location-column query; no schema request was made.

| submission | predicate / purpose | outcome |
|---|---|---|
| scry_1.json | hasAllTokens(search_text_lc,['inner','product','functional','encryption','lwe']); select id,title,doi,primary_location.landing_page_url,publication_year; order year,citations; limit25 | 1 row; record78359003-181f-4080-ac30-929b89a62fb9; spend0 |
| scry_2.json | hasAllTokens(...,['inner','product','encryption','lattice']) OR same with 'lattices'; same fields/order; limit25 | 8 rows; recorda385cc6d-6838-488c-b316-4fb182c257f8; spend0; discovered HYL2025 title |
| scry_3.json | exact doi_norm='10.1007/978-3-032-01881-6_6'; id,title,locations,open_access,abstract_inverted_index; limit3 | query_capacity_exhausted after45s; counted, not retried |
| scry_4.json | hasAllTokens(...,['unbounded','inner','product','roy']); id,title,doi,locations,abstract_inverted_index; limit10 | query_capacity_exhausted after45s; counted, not retried |

[SOURCE search limits] Successful responses identify the OpenAlex bounded
snapshot, with freshness lag approximately6,412,600 seconds at this run.
The helper states ePrint is not itself an indexed relation. Therefore a
missing Scry row is not evidence of absence from ePrint or current literature.

## Reproduction and integrity

[EXECUTED] `pdftotext -layout` created ignored extracts only. `pdftoppm -f 28
-l 29 -scale-to 1650 -png` rendered HYL pp28–29; both full pages were visually
inspected with the PDF skill. No source PDF was authored or edited.
`python3 public_arithmetic.py > public_arithmetic.stdout.json` performs public
integer checks and writes results.json; these JSON files are byte-identical.
`pin_artifacts.py` records SHA256 for all named source/fixture inputs and
all final owned artifacts. No full source text/PDF is proposed for commit.
