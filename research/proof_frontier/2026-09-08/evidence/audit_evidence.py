from pathlib import Path
import json
root=Path(__file__).parent
x=json.loads((root/'arklib-axiom-baseline.json').read_text())
names=['RS_correlatedAgreement_affineLines_uniqueDecodingRegime','RS_jointAgreement_of_goodCoeffs_card_gt','RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one']
for name in names:
 for category, entries in x.items():
  print(name,category,[e for e in entries if name in str(e)])
old=Path('/Users/ember/src/ArkLib-2026-09/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean')
print('pinned current JointAgreement equals local source:',old.read_bytes()==(root/'arklib-JointAgreement.lean').read_bytes())
print('source evidence note lines:',len((root.parent/'FRONTIER.md').read_text().splitlines()))
