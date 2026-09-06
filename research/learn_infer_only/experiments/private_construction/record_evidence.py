#!/usr/bin/env python3
"""Record local source/version hashes and commands without copying the paper corpus."""
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')


def hashed(path):
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size}


SOURCES = [
    ("2012/733", "2013-03-24", "Reusable Garbled Circuits and Succinct Functional Encryption",
     "construction and game read: Def4.1 p30, section4.1 pp31-32; chaining discussion Remark3.7 p23; introduction p7; no full reduction audit"),
    ("2015/017", "2015-10-01", "Simple Functional Encryption Schemes for Inner Products",
     "Fig2/Def2.3 pp6-7, Construction3.1/Theorem3.2/proof sketch pp7-8 read; Construction6.5 and homomorphism pp22-23 read; generic/LWE security proofs not audited"),
    ("2024/1294", "local pinned file", "Don't Trust Setup! New Directions in Pre-Constrained Cryptography",
     "local syntax/game/construction source excerpts plus prior landed audit consumed; section3.1 pp15-16; no new full reduction audit"),
    ("2016/654", "local pinned file", "Stronger Security for Reusable Garbled Circuits, General Definitions and Attacks",
     "abstract and introductory contribution discussion inspected only; not used to justify a security or exposure conclusion"),
    ("2015/608", "2016-11-21", "Fully Secure Functional Encryption for Inner Products, from Standard Assumptions",
     "section4.1 integer construction pp11-13 and section4.2 modular construction/issuance trap pp16-18 read; AppendixA Def8 adaptive IND-CPA pp30-31; Theorem3 p18 and reduction Theorem4 pp20-22 statements and supporting lemma statements inspected; no full QPT reduction audit"),
    ("2021/46", "local pinned file", "Efficient Lattice-Based Inner-Product Functional Encryption",
     "section2.3 IND game pp9-10; section4 selective RLWE construction/Theorem3 and hybrid proof pp16-20 inspected; section5 distinct adaptive construction/Theorem4 pp21-22; section7 implementation and selective-scheme cost Table1 pp24-27 read; source table medium PQ estimate119.2 conflicts with prose129; practical author code audited separately, not a full cryptographic reduction audit"),
    ("2023/721", "local pinned file", "A Fast RLWE-Based IPFE Library and its Application to Privacy-Preserving Biometric Authentication",
     "abstract/intro and section3.4 selective construction pp4-5 read; parameter/performance/OpenMP-AVX2 implementation sections inspected; later biometric protocol proof not audited; no independent security estimate or timing reproduction"),
]


def main():
    sources = []
    for ident, version, title, access in SOURCES:
        pdf = MIRROR / (ident + '.pdf')
        sources.append({"id": ident, "title": title, "version": version, "access": access,
                        "source_url": 'https://eprint.iacr.org/' + ident,
                        "local_file": hashed(pdf),
                        "instrument": ['pdftotext', '-layout', str(pdf), '<lane scratch text>'],
                        "downloaded_pdf": False})
    records = []
    for name in ('scry_reusable_garbling.json', 'scry_ipfe.json', 'scry_lattice_ipfe.json'):
        path = HERE / 'sources' / name
        raw = path.read_text().strip()
        data = json.loads(raw)
        records.append({"file": hashed(path), "record_id": data.get('record_id'),
                        "billing_mode": data.get('billing_mode'),
                        "spend_nanodollars": data.get('spend_nanodollars'),
                        "row_count": data.get('row_count'), "truncated": data.get('truncated')})
    import cryptography
    import cryptography.hazmat.bindings._rust as rust
    manifest = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "sources": sources,
        "web_primary_reads": [
            {"url": 'https://www.rfc-editor.org/rfc/rfc3526.html',
             "access": 'section3 2048-bit prime and generator2 read; parameter copied to additive_ipfe.py; no security-bit assertion'},
            {"url": 'https://cryptography.io/en/latest/hazmat/primitives/aead/',
             "access": 'AESGCM API/nonce/key/tag requirements; installed version separately pinned, latest page was 51.0.0-dev1'},
            {"url": 'https://doi.org/10.1145/2488608.2488678',
             "access": 'open returned Internal Error; no claim supported by that fetch'},
            {"url": 'https://github.com/fentec-project/IPFE-RLWE',
             "access": 'primary README, pinned shallow source clone283975175b2407ab5a77e718e254d4d01671ca3a; source audit and exact decoder function execution recorded in rlwe_source_results.json'},
            {"url": 'https://github.com/s-adhikary/IPFE',
             "access": 'primary README, pinned shallow source clone06801d086b1468cdf1a5db84ef9f43552035f3f1; source audit and exact serial decoder function execution recorded in rlwe_source_results.json'}],
        "search_accounting": {"scry_schema_calls": 1, "scry_sql_queries": 3, "kagi_queries": 0,
                              "web_search_queries": 11, "scry_records": records,
                              "scry_schema_file": hashed(HERE / 'sources' / 'scry_schema_openalex.txt'),
                              "scry_key_exposed": False, "scry_retries": 0},
        "environment": {"python": sys.version, "executable": sys.executable, "platform": platform.platform(),
                        "cryptography_version": importlib.metadata.version('cryptography'),
                        "cryptography_init": hashed(Path(cryptography.__file__)),
                        "cryptography_binary": hashed(Path(rust.__file__)),
                        "pdftotext_version": subprocess.run(['pdftotext', '-v'], capture_output=True, text=True).stderr.strip()},
        "execution_commands_from_repo_root": [
            'python3 research/learn_infer_only/experiments/private_construction/bounded_tree.py audit > research/learn_infer_only/experiments/private_construction/audit.stdout.txt',
            'python3 research/learn_infer_only/experiments/private_construction/additive_ipfe.py > research/learn_infer_only/experiments/private_construction/ipfe.stdout.txt',
            'python3 research/learn_infer_only/experiments/private_construction/lwe_additive.py > research/learn_infer_only/experiments/private_construction/lwe.stdout.txt',
            'make -C research/learn_infer_only/experiments/private_construction/vendor/IPFE-RLWE/src > research/learn_infer_only/experiments/private_construction/rlwe_build.stdout.txt 2>&1 (exit2: AVX2/arm64)',
            'python3 research/learn_infer_only/experiments/private_construction/rlwe_source_audit.py > research/learn_infer_only/experiments/private_construction/rlwe_source.stdout.txt',
            'python3 research/learn_infer_only/experiments/private_construction/record_evidence.py'],
        "artifacts": [hashed(HERE / n) for n in ('bounded_tree.py', 'additive_ipfe.py', 'lwe_additive.py',
                      'audit.stdout.txt', 'ipfe.stdout.txt', 'lwe.stdout.txt', 'results/results.json',
                      'results/ipfe_results.json', 'results/lwe_results.json', 'results/synthetic_deployment.json',
                      'rlwe_source_audit.py', 'RLWE_AUDIT.md', 'rlwe_source.stdout.txt', 'rlwe_build.stdout.txt',
                      'results/rlwe_source_results.json', 'EXTRACTED_CODE_LICENSES.md', '.gitignore')],
        "limitations": ['source PDFs remain in read-only mirror; scratch text copies need not be committed',
                        'cryptographic correctness tests are not security proof execution',
                        'honest initialization erasure is assumed, not verified']}
    (HERE / 'sources_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({"local_sources_hashed": len(sources), "scry_sql_queries": 3,
                      "scry_spend_nanodollars": sum(r['spend_nanodollars'] for r in records)}, indent=2))


if __name__ == '__main__':
    main()
