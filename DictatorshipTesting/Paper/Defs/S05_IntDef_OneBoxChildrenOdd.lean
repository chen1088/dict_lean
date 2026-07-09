import DictatorshipTesting.Paper.Defs.S05_IntDef_VerticalTwoStripChildrenEven
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_11_OneBoxRemovals`
- `DictatorshipTesting.Paper.Defs.S05_Def5_27_CertificateExceptionalPredicates`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_ZEven`
- `DictatorshipTesting.Paper.S05_Int_TableauDimension`
-/


/-!
Definition file for `oneBoxChildrenOdd`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- One-box children specialized to diagrams with `2*m+1` boxes. -/
def oneBoxChildrenOdd (m : ℕ)
    (lam : YoungDiagram (2 * m + 1)) : Finset (YoungDiagram (2 * m)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (2 * m) =>
    IsOneBoxChild lam mu)

end DictatorshipTesting
