import DictatorshipTesting.Paper.Defs.S05_IntDef_VerticalTwoStripChildren
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_02_RemovableCorners`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_HorizontalTwoStripChildrenEven`
-/


/-!
Definition file for `oneBoxChildren`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- One-box children in the ordinary branching rule. -/
def oneBoxChildren {n : ℕ}
    (lam : YoungDiagram n) : Finset (YoungDiagram (n - 1)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (n - 1) =>
    IsOneBoxChild lam mu)

end DictatorshipTesting
