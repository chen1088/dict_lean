import DictatorshipTesting.Paper.Defs.S03_Def3_12_CubeHighDegreeEnergy

/-!
Definition file for `cubeSquareEnergy`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Mean square of the mixed second difference under the square-test directions. -/
def cubeSquareEnergy {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  (∑ x : Cube m,
      (∑ c : CubeDirectionColor m,
        (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ)) /
    (Fintype.card (Cube m) : ℝ)

end DictatorshipTesting
