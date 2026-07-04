import DictatorshipTesting.Paper.Aux_YoungAdjacentEntries

/-!
Paper statement: Lemma 5.1 (`lem:young-adjacent-matrices`)
Title in paper: Adjacent transpositions in Young's basis.

Status: this file contains the first basis-level tableau facts needed for
Lemma 5.1.  The actual Young orthogonal representation matrices remain future
work.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.1 basis-level component: adjacent entries occupy distinct cells. -/
theorem S05_Lem5_01_adjacent_cells_distinct {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentLoCell T a ≠ adjacentHiCell T a := by
  exact adjacentLoCell_ne_hiCell T a

/-- Lemma 5.1 basis-level component: in a common row, the lower adjacent entry
is to the left. -/
theorem S05_Lem5_01_adjacent_col_lt_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentLoCell T a) <
      YoungCell.col (adjacentHiCell T a) := by
  exact adjacent_col_lt_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: in a common column, the lower adjacent
entry is above. -/
theorem S05_Lem5_01_adjacent_row_lt_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.row (adjacentLoCell T a) <
      YoungCell.row (adjacentHiCell T a) := by
  exact adjacent_row_lt_of_sameCol T a hcol

end DictatorshipTesting
