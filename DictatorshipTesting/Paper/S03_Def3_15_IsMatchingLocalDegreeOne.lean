import DictatorshipTesting.Paper.S03_Def3_14_PermInner

/-!
Definition file for `IsMatchingLocalDegreeOne`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A function is locally degree one on every matching cube for `M`. -/
def IsMatchingLocalDegreeOne {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : Prop :=
  ∀ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x)) = 0

end DictatorshipTesting
