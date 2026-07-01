import DictatorshipTesting.Paper.Aux_CubeCharKernel

/-!
# Lemma 2.3: cube Fourier expansion

This proves the second displayed identity in `lem:cube-parseval`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The Fourier expansion part of Lemma 2.3, `lem:cube-parseval`. -/
theorem L2_3_cubeFourier_expansion (m : ℕ) :
    ∀ g : Cube m → ℝ, ∀ x : Cube m,
      g x = ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x := by
  intro g x
  classical
  let N : ℝ := Fintype.card (Cube m)
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast Fintype.card_ne_zero
  symm
  calc
    ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x
        = (∑ y : Cube m, g y *
            (∑ S : Finset (Fin m), cubeChar S y * cubeChar S x)) / N := by
          calc
            ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x
                =
                ∑ S : Finset (Fin m),
                  (((∑ y : Cube m, g y * cubeChar S y) / N) * cubeChar S x) := by
                    simp [cubeFourierCoeff, cubeExpectation, N]
            _ = ∑ S : Finset (Fin m),
                  ∑ y : Cube m, (g y * cubeChar S y * cubeChar S x) / N := by
                    apply Finset.sum_congr rfl
                    intro S _
                    rw [← Finset.sum_div]
                    rw [div_mul_eq_mul_div]
                    rw [Finset.sum_mul]
            _ = ∑ y : Cube m,
                  ∑ S : Finset (Fin m), (g y * cubeChar S y * cubeChar S x) / N := by
                    exact Finset.sum_comm
            _ = ∑ y : Cube m,
                  (g y * (∑ S : Finset (Fin m), cubeChar S y * cubeChar S x)) / N := by
                    apply Finset.sum_congr rfl
                    intro y _
                    rw [← Finset.sum_div]
                    simp [Finset.mul_sum, mul_left_comm, mul_comm]
            _ = (∑ y : Cube m, g y *
                    (∑ S : Finset (Fin m), cubeChar S y * cubeChar S x)) / N := by
                    rw [Finset.sum_div]
    _ = (∑ y : Cube m, g y * (if x = y then N else 0)) / N := by
          congr 1
          apply Finset.sum_congr rfl
          intro y _
          rw [cubeChar_kernel x y]
    _ = (g x * N) / N := by
          congr 1
          rw [Finset.sum_eq_single x]
          · simp
          · intro y _ hy
            simp [hy.symm]
          · intro hx
            exact (hx (Finset.mem_univ x)).elim
    _ = g x := by
          field_simp [hN]

end DictatorshipTesting
