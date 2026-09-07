# Search accounting for lockable gate audit

[EXECUTED] Existing schema from
`../sources/scry_schema_openalex.txt` reused; no schema request in this tranche.
The helper `swarm/tools/scry.py` read the existing user credential without
printing it. Calls used `SCRY_MAX_SECONDS=45`. No PDF was downloaded.

[EXECUTED] SQL call 1, saved `scry_discovery.json`, record
`c89c234c-fc9b-43be-833f-86815f38a565`, 12 rows, spend 0 nanodollars:

```sql
SELECT id,title,doi,primary_location.landing_page_url,locations
FROM openalex.works
WHERE hasToken(search_text_lc,'lockable')
   OR hasAllTokens(search_text_lc,['compute','compare','obfuscation'])
ORDER BY cited_by_count DESC LIMIT 12
```

[EXECUTED] This was overly broad: unrelated uses of “lockable” dominated.
SQL call 2, saved `scry_refined.json`, record
`20e97c28-b15f-46df-b97f-b506c537433f`, 7 rows, spend 0 nanodollars:

```sql
SELECT id,title,doi,primary_location.landing_page_url,publication_year
FROM openalex.works
WHERE hasAllTokens(search_text_lc,['lockable','obfuscation'])
   OR hasAllTokens(search_text_lc,['compute','compare','obfuscation'])
ORDER BY cited_by_count DESC LIMIT 18
```

[REPORTED] Two web search queries in one call located primary IDs:

- `"Obfuscating Compute-and-Compare Programs" LWE Wichs Zirdelis eprint`
- `"Lockable Obfuscation" Goyal Koppula Waters eprint`

The indexed results identified 2017/276 and 2017/274, and a correctness follow-up
2019/1010. Full source inspection used only the local absolute mirror paths in
`results.json`, not web PDF downloads. The mirrored 2019/1010 was dated
September9,2019, unlike a later revision shown in web metadata. Claims are scoped
to the bytes actually read.

[REPORTED] Tranche totals SQL2/schema0/web2/Kagi0; cumulative lane totals
SQL10/schema1/web30/Kagi0. No timeout, retry or additional query.
