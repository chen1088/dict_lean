import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungCells
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDimNat`
-/


/-!
Definition file for `youngHookLength`.
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
