import DictatorshipTesting.Paper.Aux_BoolSignMulEqNegOne
import DictatorshipTesting.Paper.Aux_CubeCharFinsetToggle
import DictatorshipTesting.Paper.Aux_CubeCharMulSelf
import DictatorshipTesting.Paper.Aux_FinsetToggleInvolutive

open scoped BigOperators

namespace DictatorshipTesting

/-- Dual orthogonality of Boolean-cube characters, summing over character supports. -/
theorem cubeChar_kernel {m : ℕ} (x y : Cube m) :
    (∑ S : Finset (Fin m), cubeChar S y * cubeChar S x) =
      if x = y then (Fintype.card (Cube m) : ℝ) else 0 := by
  classical
  by_cases hxy : x = y
  · rw [if_pos hxy]
    subst y
    have hcard : Fintype.card (Finset (Fin m)) = Fintype.card (Cube m) := by
      simp [Cube, Fintype.card_finset]
    calc
      (∑ S : Finset (Fin m), cubeChar S x * cubeChar S x)
          = ∑ _S : Finset (Fin m), (1 : ℝ) := by
              simp [cubeChar_mul_self]
      _ = (Fintype.card (Finset (Fin m)) : ℝ) := by
              simp
      _ = (Fintype.card (Cube m) : ℝ) := by
              exact_mod_cast hcard
  · have hex : ∃ r : Fin m, x r ≠ y r := by
      by_contra h
      apply hxy
      ext r
      exact not_not.mp (not_exists.mp h r)
    rcases hex with ⟨r, hr⟩
    have hsum :
        (∑ S : Finset (Fin m), cubeChar S y * cubeChar S x) = 0 := by
      simpa using
        (Finset.sum_involution
          (s := (Finset.univ : Finset (Finset (Fin m))))
          (f := fun S => cubeChar S y * cubeChar S x)
          (g := fun S _ => finsetToggle r S)
          (by
            intro S _
            rw [cubeChar_finsetToggle r S y, cubeChar_finsetToggle r S x]
            have hsign : ((if y r then (-1 : ℝ) else 1) *
                (if x r then (-1 : ℝ) else 1)) = -1 := by
              exact boolSign_mul_eq_neg_one_of_ne (by exact fun h => hr h.symm)
            calc
              cubeChar S y * cubeChar S x +
                  (if y r then (-1 : ℝ) else 1) * cubeChar S y *
                    ((if x r then (-1 : ℝ) else 1) * cubeChar S x)
                  =
                  cubeChar S y * cubeChar S x +
                    (((if y r then (-1 : ℝ) else 1) *
                      (if x r then (-1 : ℝ) else 1)) *
                      (cubeChar S y * cubeChar S x)) := by ring
              _ = 0 := by
                rw [hsign]
                ring)
          (by
            intro S _ _ hfix
            have hmem := congr_arg (fun T : Finset (Fin m) => r ∈ T) hfix
            by_cases hS : r ∈ S <;> simp [finsetToggle, hS] at hmem)
          (by
            intro S _
            simp)
          (by
            intro S _
            exact finsetToggle_involutive r S))
    simp [hxy, hsum]

end DictatorshipTesting
