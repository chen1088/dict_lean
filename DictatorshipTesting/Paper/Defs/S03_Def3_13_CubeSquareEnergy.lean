import DictatorshipTesting.Paper.Defs.S03_Def3_12_CubeHighDegreeEnergy
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_14_PermInner`
- `DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare`
-/


/-!
Definition file for `cubeSquareEnergy`.
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
