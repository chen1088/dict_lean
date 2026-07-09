import DictatorshipTesting.Paper.S03_Def3_15_IsMatchingLocalDegreeOne

/-!
Definition file for `matchingLocalHighDegreeEnergy`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Average local high-degree Fourier energy over all base permutations. -/
def matchingLocalHighDegreeEnergy {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  (∑ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x))) /
    (Fintype.card (Perm α) : ℝ)

end DictatorshipTesting
