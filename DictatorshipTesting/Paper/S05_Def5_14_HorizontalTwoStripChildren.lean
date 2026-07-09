import DictatorshipTesting.Paper.S05_Def5_13_IsOneBoxChild

/-!
Definition file for `horizontalTwoStripChildren`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
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
