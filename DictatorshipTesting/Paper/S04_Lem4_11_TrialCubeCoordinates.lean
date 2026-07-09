import DictatorshipTesting.Paper.Defs.S03_Def3_09_MatchingTrialDelta
import DictatorshipTesting.Paper.S03_Int_OrderedMatchingTauMul

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
# Lemma 4.11: One trial in cube coordinates

This is `lem:trial-cube-coordinates` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Lemma 4.11, `lem:trial-cube-coordinates`: one trial in cube coordinates. -/
theorem L4_11_TrialCubeCoordinates {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α)
    (x : Cube M.edgeCount) (c : CubeDirectionColor M.edgeCount) :
    matchingTrialDelta f M (π * M.tau x) c =
      cubeDelta (fun y => boolToReal (matchingCubeRestriction f M π y))
        x (cubeColorU c) (cubeColorV c) := by
  simp [matchingTrialDelta, matchingCubeRestriction, cubeDelta,
    orderedMatching_tau_mul, cubeXor_zero, cubeZero_xor, cubeXor_assoc,
    mul_assoc]

end DictatorshipTesting
