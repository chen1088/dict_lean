import DictatorshipTesting.Paper.Defs.S05_IntDef_VerticalTwoStripChildrenEven

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
