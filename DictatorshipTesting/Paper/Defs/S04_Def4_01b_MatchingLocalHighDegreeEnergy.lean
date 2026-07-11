import DictatorshipTesting.Paper.Defs.S04_Def4_01a_IsMatchingLocalDegreeOne
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S04_Def4_02a_MatchingLocalProjection`
-/


/-!
Definition file for `matchingLocalHighDegreeEnergy`.
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
