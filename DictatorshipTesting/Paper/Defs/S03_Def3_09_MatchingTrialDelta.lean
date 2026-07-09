import DictatorshipTesting.Paper.Defs.S03_Def3_08_CubeColorV

/-!
Definition file for `matchingTrialDelta`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The real mixed second difference queried by one matching-cube trial. -/
def matchingTrialDelta {α : Type*} [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α)
    (c : CubeDirectionColor M.edgeCount) : ℝ :=
  cubeDelta (fun x => boolToReal (matchingCubeRestriction f M π x))
    (cubeZero M.edgeCount) (cubeColorU c) (cubeColorV c)

end DictatorshipTesting
