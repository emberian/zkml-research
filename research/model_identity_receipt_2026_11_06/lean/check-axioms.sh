#!/bin/sh
# The pinned axiom footprint of the receipt theorems: exits 1 if it changes.
cd "$(dirname "$0")" && lake env lean PrintAxioms.lean | diff - axioms.expected && echo "axioms: as pinned"
