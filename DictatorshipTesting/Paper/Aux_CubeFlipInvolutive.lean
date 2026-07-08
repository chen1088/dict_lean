import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality`
- `DictatorshipTesting.Paper.S04_Lem4_08_TijLocalDegree`
-/

namespace DictatorshipTesting

/-- Flipping the same Boolean-cube coordinate twice is the identity. -/
theorem cubeFlip_involutive {m : ℕ} (r : Fin m) (x : Cube m) :
    cubeFlip r (cubeFlip r x) = x := by
  ext s
  by_cases hs : s = r <;> simp [cubeFlip, hs]

end DictatorshipTesting
