import Selvage.ArityEightLoggedWitnesses
open Minidregg.Selvage.ArityEight
open Minidregg.Selvage.ArityEight.Witnesses
open Minidregg.Selvage.ArityEight.Witnesses.Logged

-- All 17 scalar challenges: accepted row, false equation, malformed supplied path.
#eval ((List.ofFn fun β : Fin 17 =>
  rowCheck H D₀ D₁ D₂ sourceRoot inputRoot nextRoot (β.val:F) 0 (row 0)).all id,
  (List.ofFn fun β : Fin 17 =>
    !(rowCheck H D₀ D₁ D₂ sourceRoot inputRoot nextRoot (β.val:F) 1 (row 1))).all id,
  (List.ofFn fun β : Fin 17 =>
    let o := row 0
    let broken : RowOpening F Digest := { o with source := fun c b a =>
      ⟨(o.source c b a).value, []⟩ }
    !(rowCheck H D₀ D₁ D₂ sourceRoot inputRoot nextRoot (β.val:F) 0 broken)).all id)
#eval checkpoint.length
