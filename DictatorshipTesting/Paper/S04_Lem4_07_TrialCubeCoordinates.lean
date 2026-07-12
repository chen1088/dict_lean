import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingTrialDelta
import DictatorshipTesting.Paper.S03_Int_OrderedMatchingTauMul
import DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Prop4_08_SquareEnergyControlsGlobalDegree`
-/


/-!
# Lemma 4.7: One trial in cube coordinates

This is `lem:trial-cube-coordinates` from `dictatorship_testing_stoc27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Lemma 4.7, `lem:trial-cube-coordinates`: one trial in cube coordinates. -/
theorem S04_Lem4_07_TrialCubeCoordinates {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α)
    (x : Cube M.edgeCount) (c : CubeDirectionColor M.edgeCount) :
    matchingTrialDelta f M (π * M.tau x) c =
      cubeDelta (fun y => boolToReal (matchingCubeRestriction f M π y))
        x (cubeColorU c) (cubeColorV c) := by
  simp [matchingTrialDelta, matchingCubeRestriction, cubeDelta,
    orderedMatching_tau_mul, cubeXor_zero, cubeZero_xor, cubeXor_assoc,
    mul_assoc]

end DictatorshipTesting
