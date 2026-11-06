"""Streaming-receipt window counts (breadstuffs initiative 11, docs/stream/).

Extends space.py's certificate model; imports its constants, forks nothing:
    python3 notes/construction-search/stream_counts.py [W] [N] [ENTRY_BYTES]

One window = W entries appended at log height N. Per entry the window certificate needs:
  monitor step       table routing over the product automaton (4 states x 4 symbols = 16 rows)
                     [space.CERT_FAMILIES["dfa-table-routing"]: 3 cells, 1 lookup]
  classifier         the symbol must come from the committed bytes. Today it is Lean's JSON reader
                     (Stream.ClaudeCore.classify), not an automaton. Two [INFERRED] bounds:
                     byte DFA (3 cells + 1 lookup per byte) if the classifier compiles to one,
                     bracket replay (24 cells, 2 lookups, 4 chip perms per token, one token per byte)
                     for the JSON nesting it actually reads.
  entry digest       commitment_perms(bytes) Poseidon2 permutations (hash_bytes_8)
  leaf hash          1 permutation (MMR leaf, arity 1)
  carries            amortized < 1 permutation per entry (W + popcount(N) - popcount(N+W) merges)
Per window: bagging popcount(N+W) + 1 permutations. The follower's native bill (blake3, measured by
`stream-check`) is 2W + merges + popcount(N+W) + 1 hash calls; it has the same shape.
"""
import importlib.util
import os
import sys

_spec = importlib.util.spec_from_file_location(
    "space", os.path.join(os.path.dirname(os.path.abspath(__file__)), "space.py"))
space = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(space)

PERM = space.INCIRCUIT_CELLS["poseidon2"]
DFA_CELLS, DFA_LK, _, _ = space.CERT_FAMILIES["dfa-table-routing"]
BR_CELLS, BR_LK, BR_CHIP, _ = space.CERT_FAMILIES["bracket-replay"]
POLICY_TABLE_ROWS = 4 * 4


def window(w, n, entry_bytes):
    merges = w + bin(n).count("1") - bin(n + w).count("1")
    bag = bin(n + w).count("1") + 1
    digest = space.commitment_perms(entry_bytes)
    hash_perms = w * (digest + 1) + merges + bag
    monitor = w * DFA_CELLS
    cls_dfa = w * entry_bytes * DFA_CELLS
    cls_vpa = w * entry_bytes * (BR_CELLS + BR_CHIP * PERM)
    return dict(merges=merges, bag=bag, hash_perms=hash_perms, hash_cells=hash_perms * PERM,
                monitor_cells=monitor, monitor_lookups=w * DFA_LK,
                cls_dfa_cells=cls_dfa, cls_vpa_cells=cls_vpa,
                native_hash_calls=2 * w + merges + bag)


def main():
    w = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 2 ** 20
    sizes = [int(sys.argv[3])] if len(sys.argv) > 3 else [694, 4128]
    print(f"stream window: W={w} entries at height N={n:,}; policy table {POLICY_TABLE_ROWS} rows")
    for b in sizes:
        r = window(w, n, b)
        print(f"\n== entry {b:,} bytes")
        print(f"  Poseidon2 perms: {r['hash_perms']:,} = W*(digest {space.commitment_perms(b)} + leaf 1)"
              f" + merges {r['merges']} + bag {r['bag']}  -> {r['hash_cells']:,} cells")
        print(f"  monitor: {r['monitor_cells']:,} cells, {r['monitor_lookups']} lookups"
              f"  ({r['monitor_cells'] / r['hash_cells']:.2e} of the hash cells)")
        print(f"  classifier [INFERRED]: byte DFA {r['cls_dfa_cells']:,} cells; bracket replay {r['cls_vpa_cells']:,} cells")
        print(f"  native follower: {r['native_hash_calls']} blake3 calls (stream-check prints this per window)")
    print("\nper-window cost depends on N only through popcount (merges, bag): O(W + log N).")


if __name__ == "__main__":
    main()
