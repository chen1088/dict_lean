import DictatorshipTesting.Paper.S05_Def5_04_YoungCells

/-!
Definition file for `youngHookLength`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Hook length of a cell in a Young diagram. -/
def youngHookLength {n : ℕ} (lam : YoungDiagram n) (cell : Fin n × Fin n) : ℕ :=
  (youngRow lam cell.1 - (cell.2 : ℕ)) +
    (Finset.univ.filter (fun r : Fin n =>
      (cell.1 : ℕ) < (r : ℕ) ∧ (cell.2 : ℕ) < youngRow lam r)).card

end DictatorshipTesting
