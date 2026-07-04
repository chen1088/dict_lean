import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis

/-!
Paper statement: Lemma 5.2 (`lem:jucys-murphy-eigenbasis`)
Title in paper: Jucys--Murphy eigenbasis.

Status: this file records the basis-level content API used by the future
Jucys--Murphy statement.  The actual operator/eigenbasis theorem remains future
work in the Specht-module/tableau representation layer.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.2 basis-level vocabulary: content of a tableau cell. -/
def S05_Lem5_02_cellContent {n : Nat} {lam : YoungDiagram n}
    (u : YoungCell lam) : Int :=
  YoungCell.content u

/-- Lemma 5.2 basis-level vocabulary: content of the cell containing an entry. -/
noncomputable def S05_Lem5_02_entryContent {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T a

/-- Lemma 5.2 basis-level component: adjacent entry contents differ by `+1`
in the same-row case. -/
theorem S05_Lem5_02_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) + 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow

/-- Lemma 5.2 basis-level component: adjacent entry contents differ by `-1`
in the same-column case. -/
theorem S05_Lem5_02_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) - 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol

end DictatorshipTesting
