import DictatorshipTesting.Paper.Aux_CubeCharFlip
import DictatorshipTesting.Paper.Aux_CubeCharNonzero
import DictatorshipTesting.Paper.Aux_CubeFlipInvolutive

open scoped BigOperators

namespace DictatorshipTesting

/-- A nonempty Boolean-cube character has mean-zero numerator. -/
theorem cubeChar_sum_eq_zero_of_nonempty {m : ℕ} {S : Finset (Fin m)}
    (hS : S.Nonempty) :
    ∑ x : Cube m, cubeChar S x = 0 := by
  classical
  rcases hS with ⟨r, hr⟩
  simpa using
    (Finset.sum_involution
      (s := (Finset.univ : Finset (Cube m)))
      (f := fun x => cubeChar S x)
      (g := fun x _ => cubeFlip r x)
      (by
        intro x _
        rw [cubeChar_cubeFlip S r hr x]
        ring)
      (by
        intro x _ _ hfix
        have hcoord := congr_fun hfix r
        by_cases hx : x r <;> simp [cubeFlip, hx] at hcoord)
      (by
        intro x _
        simp)
      (by
        intro x _
        exact cubeFlip_involutive r x))

end DictatorshipTesting
