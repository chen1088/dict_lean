import DictatorshipTesting.Paper.S03_Def3_17_MatchingLocalProjection

/-!
Definition file for `matchingLocalProjectionError`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared error after removing the matching-local degree-one part. -/
def matchingLocalProjectionError {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  l2DistSq F (matchingLocalProjection M F)

end DictatorshipTesting
