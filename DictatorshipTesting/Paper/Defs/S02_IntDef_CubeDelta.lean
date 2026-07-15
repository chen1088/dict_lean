import AlgebraicLibrary.BooleanCube.Basic

open AlgebraicLibrary
/-
Direct reverse imports: none.
-/


/-!
Definition file for `cubeDelta`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The mixed second difference on a Boolean-cube square. -/
def cubeDelta {m : ℕ} (g : FinCube m → ℝ) (x u v : FinCube m) : ℝ :=
  g x - g (cubeXor x u) - g (cubeXor x v) + g (cubeXor (cubeXor x u) v)

end DictatorshipTesting
