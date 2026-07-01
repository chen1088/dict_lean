import DictatorshipTesting.Paper.Aux_FinsetToggle

namespace DictatorshipTesting

/-- Toggling a coordinate in the character support multiplies the character by
that coordinate's sign. -/
theorem cubeChar_finsetToggle {m : ℕ} (r : Fin m) (S : Finset (Fin m)) (x : Cube m) :
    cubeChar (finsetToggle r S) x =
      (if x r then (-1 : ℝ) else 1) * cubeChar S x := by
  unfold cubeChar
  by_cases hr : r ∈ S
  · rw [show finsetToggle r S = S.erase r by simp [finsetToggle, hr]]
    rw [← Finset.mul_prod_erase S (fun q => if x q then (-1 : ℝ) else 1) (a := r) hr]
    by_cases hx : x r <;> simp [hx]
  · rw [show finsetToggle r S = insert r S by simp [finsetToggle, hr]]
    rw [Finset.prod_insert hr]

end DictatorshipTesting
