import DictatorshipTesting.Paper.S03_Def3_09_MatchingTrialDelta

/-!
Definition file for `matchingTrialDeltaReal`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The real-valued mixed second difference queried by one matching-cube trial. -/
def matchingTrialDeltaReal {α : Type*} [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) (π : Perm α)
    (c : CubeDirectionColor M.edgeCount) : ℝ :=
  cubeDelta (fun x : Cube M.edgeCount => F (π * M.tau x))
    (cubeZero M.edgeCount) (cubeColorU c) (cubeColorV c)

end DictatorshipTesting
