import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S02_Int_CubeFourierTranslate`
- `DictatorshipTesting.Paper.S03_Int_OrderedMatchingTauMul`
- `DictatorshipTesting.Paper.S05_Def5_15_MatchingCharacters`
-/


/-!
# Cube characters and xor
-/

namespace DictatorshipTesting

/-- The `{1,-1}` sign of xor is the product of signs. -/
theorem boolSign_xor (a b : Bool) :
    (if a ^^ b then (-1 : ℝ) else 1) =
      (if a then (-1 : ℝ) else 1) * (if b then (-1 : ℝ) else 1) := by
  cases a <;> cases b <;> simp

/-- Boolean-cube characters multiply under coordinatewise xor. -/
theorem cubeChar_cubeXor {m : ℕ} (S : Finset (Fin m)) (x y : Cube m) :
    cubeChar S (cubeXor x y) = cubeChar S x * cubeChar S y := by
  unfold cubeChar cubeXor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _hr
  exact boolSign_xor (x r) (y r)

/-- Xor with the zero cube point on the right. -/
theorem cubeXor_zero {m : ℕ} (x : Cube m) :
    cubeXor x (cubeZero m) = x := by
  ext r
  simp [cubeXor, cubeZero]

/-- Xor with the zero cube point on the left. -/
theorem cubeZero_xor {m : ℕ} (x : Cube m) :
    cubeXor (cubeZero m) x = x := by
  ext r
  simp [cubeXor, cubeZero]

/-- Coordinatewise xor is associative. -/
theorem cubeXor_assoc {m : ℕ} (x y z : Cube m) :
    cubeXor (cubeXor x y) z = cubeXor x (cubeXor y z) := by
  ext r
  simp [cubeXor]

/-- Coordinatewise xor is commutative. -/
theorem cubeXor_comm {m : ℕ} (x y : Cube m) :
    cubeXor x y = cubeXor y x := by
  ext r
  simp [cubeXor, Bool.xor_comm]

/-- Xoring by the same point twice on the left is the identity. -/
theorem cubeXor_self_left {m : ℕ} (z x : Cube m) :
    cubeXor z (cubeXor z x) = x := by
  ext r
  by_cases hz : z r <;> simp [cubeXor, hz]

/-- Xoring by the same point twice on the right is the identity. -/
theorem cubeXor_self_right {m : ℕ} (x z : Cube m) :
    cubeXor (cubeXor x z) z = x := by
  ext r
  by_cases hz : z r <;> simp [cubeXor, hz]

/-- Translation by a fixed cube point as an equivalence. -/
def cubeXorEquiv {m : ℕ} (z : Cube m) : Cube m ≃ Cube m where
  toFun x := cubeXor z x
  invFun x := cubeXor z x
  left_inv := cubeXor_self_left z
  right_inv := cubeXor_self_left z

end DictatorshipTesting
