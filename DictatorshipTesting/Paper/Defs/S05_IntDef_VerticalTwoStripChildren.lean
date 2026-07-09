import DictatorshipTesting.Paper.Defs.S05_IntDef_HorizontalTwoStripChildren
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_09_TwoBoxRemovals`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_OneBoxChildren`
-/


/-!
Definition file for `verticalTwoStripChildren`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Vertical two-strip children in the domino branching rule. -/
def verticalTwoStripChildren {n : ℕ}
    (lam : YoungDiagram n) : Finset (YoungDiagram (n - 2)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (n - 2) =>
    IsVerticalTwoStripChild lam mu)

end DictatorshipTesting
