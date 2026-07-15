import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeDelta
import DictatorshipTesting.Paper.Defs.S03_IntDef_CubeDirectionColor
import DictatorshipTesting.Paper.Defs.S03_IntDef_CubeColorU
import DictatorshipTesting.Paper.Defs.S03_IntDef_CubeColorV
import AlgebraicLibrary.BooleanCube.LowDegree

open AlgebraicLibrary
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_PermInner`
- `DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare`
-/


/-!
Definition file for `cubeSquareEnergy`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Mean square of the mixed second difference under the square-test directions. -/
def cubeSquareEnergy {m : ℕ} (g : FinCube m → ℝ) : ℝ :=
  (∑ x : FinCube m,
      (∑ c : CubeDirectionColor m,
        (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ)) /
    (Fintype.card (FinCube m) : ℝ)

end DictatorshipTesting
