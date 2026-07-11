import DictatorshipTesting.Paper.Defs.S04_Def4_02a_MatchingLocalProjection
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S03_IntDef_NearPerfectMatching`
- `DictatorshipTesting.Paper.S04_Lem4_04_LocalHighDegreeErrorFormula`
- `DictatorshipTesting.Paper.S04_Lem4_05_PMPerpendicular`
-/


/-!
Definition file for `matchingLocalProjectionError`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared error after removing the matching-local degree-one part. -/
def matchingLocalProjectionError {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  l2DistSq F (matchingLocalProjection M F)

end DictatorshipTesting
