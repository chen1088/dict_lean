import DictatorshipTesting.Paper.Defs.S05_IntDef_IsOneBoxChild
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_VerticalTwoStripChildren`
-/


/-!
Definition file for `horizontalTwoStripChildren`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Horizontal two-strip children in the domino branching rule. -/
def horizontalTwoStripChildren {n : ℕ}
    (lam : YoungDiagram n) : Finset (YoungDiagram (n - 2)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (n - 2) =>
    IsHorizontalTwoStripChild lam mu)

end DictatorshipTesting
