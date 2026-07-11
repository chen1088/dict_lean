import DictatorshipTesting.Paper.S05_IntInst_YoungDiagramFintype
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_13a_CertificateSpecialDiagrams`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_YoungCells`
-/


/-!
Definition file for `youngRow`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Row length of a Young diagram, extended by zero past the last represented
row.  Row and column indices are zero-based. -/
def youngRow {n : ℕ} (lam : YoungDiagram n) (i : ℕ) : ℕ :=
  if h : i < n then (lam.row ⟨i, h⟩ : ℕ) else 0

end DictatorshipTesting
