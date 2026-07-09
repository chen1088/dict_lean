import DictatorshipTesting.Paper.Aux_Def_VerticalTwoStripChildren

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
