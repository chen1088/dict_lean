import DictatorshipTesting.Paper.Defs.S03_Def3_17_MatchingLocalProjection
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_19_NearPerfectMatching`
- `DictatorshipTesting.Paper.S04_Lem4_06_LocalHighDegreeErrorFormula`
- `DictatorshipTesting.Paper.S04_Lem4_07_PMPerpendicular`
-/


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
