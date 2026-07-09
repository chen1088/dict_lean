import DictatorshipTesting.Paper.Defs.S05_IntDef_HorizontalTwoStripChildrenEven
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_OneBoxChildrenOdd`
-/


/-!
Definition file for `verticalTwoStripChildrenEven`.
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
