import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingTrialDelta

open AlgebraicLibrary
/-
Direct reverse imports: none.
-/


/-!
Definition file for `matchingTrialDeltaReal`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The real-valued mixed second difference queried by one matching-cube trial. -/
def matchingTrialDeltaReal {α : Type*} [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) (π : Perm α)
    (c : CubeDirectionColor M.edgeCount) : ℝ :=
  cubeDelta (fun x : FinCube M.edgeCount => F (π * M.tau x))
    (finCubeZero M.edgeCount) (cubeColorU c) (cubeColorV c)

end DictatorshipTesting
