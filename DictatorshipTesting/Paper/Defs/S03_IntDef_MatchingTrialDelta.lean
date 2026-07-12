import DictatorshipTesting.Paper.Defs.S03_IntDef_CubeColorV
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingTrialDeltaReal`
- `DictatorshipTesting.Paper.S03_Lem3_02_PerfectCompleteness`
- `DictatorshipTesting.Paper.S04_Lem4_07_TrialCubeCoordinates`
-/


/-!
Definition file for `matchingTrialDelta`.
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
