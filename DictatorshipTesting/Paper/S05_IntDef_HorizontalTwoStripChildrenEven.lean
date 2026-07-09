import DictatorshipTesting.Paper.S05_IntDef_OneBoxChildren

/-!
Definition file for `horizontalTwoStripChildrenEven`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Horizontal two-strip children specialized to diagrams with `2*m` boxes. -/
def horizontalTwoStripChildrenEven (m : ℕ)
    (lam : YoungDiagram (2 * m)) : Finset (YoungDiagram (2 * (m - 1))) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (2 * (m - 1)) =>
    IsHorizontalTwoStripChild lam mu)

end DictatorshipTesting
