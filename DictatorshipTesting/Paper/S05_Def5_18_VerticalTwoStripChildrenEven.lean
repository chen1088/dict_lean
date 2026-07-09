import DictatorshipTesting.Paper.S05_Def5_17_HorizontalTwoStripChildrenEven

/-!
Definition file for `verticalTwoStripChildrenEven`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Vertical two-strip children specialized to diagrams with `2*m` boxes. -/
def verticalTwoStripChildrenEven (m : ℕ)
    (lam : YoungDiagram (2 * m)) : Finset (YoungDiagram (2 * (m - 1))) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (2 * (m - 1)) =>
    IsVerticalTwoStripChild lam mu)

end DictatorshipTesting
