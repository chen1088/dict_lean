import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungRow
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_01_YoungDiagramsAndBoxes`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_YoungHookLength`
-/


/-!
Definition file for `youngCells`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The cells of a Young diagram, represented as zero-based row-column pairs. -/
def youngCells {n : ℕ} (lam : YoungDiagram n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun cell : Fin n × Fin n =>
    (cell.2 : ℕ) < youngRow lam cell.1)

end DictatorshipTesting
