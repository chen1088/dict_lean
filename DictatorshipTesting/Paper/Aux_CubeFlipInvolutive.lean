import DictatorshipTesting.Paper.Defs

namespace DictatorshipTesting

/-- Flipping the same Boolean-cube coordinate twice is the identity. -/
theorem cubeFlip_involutive {m : ℕ} (r : Fin m) (x : Cube m) :
    cubeFlip r (cubeFlip r x) = x := by
  ext s
  by_cases hs : s = r <;> simp [cubeFlip, hs]

end DictatorshipTesting
