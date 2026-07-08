import DictatorshipTesting.Paper.Defs
import DictatorshipTesting.Paper.Aux_CubeCharMulSelf

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper`
- `DictatorshipTesting.Paper.Aux_CubeLowDegreeError`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity`
-/

/-!
# Lemma 2.3: cube Fourier expansion

This proves the second displayed identity in `lem:cube-parseval`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Toggle membership of one element in a finset. -/
def finsetToggle {α : Type*} [DecidableEq α] (a : α) (S : Finset α) : Finset α :=
  if a ∈ S then S.erase a else insert a S

/-- Toggling the same finset element twice is the identity. -/
theorem finsetToggle_involutive {α : Type*} [DecidableEq α] (a : α) (S : Finset α) :
    finsetToggle a (finsetToggle a S) = S := by
  by_cases h : a ∈ S <;> simp [finsetToggle, h]

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

/-- Distinct Boolean bits have opposite `{1,-1}` signs. -/
theorem boolSign_mul_eq_neg_one_of_ne {a b : Bool} (h : a ≠ b) :
    ((if a then (-1 : ℝ) else 1) * (if b then (-1 : ℝ) else 1)) = -1 := by
  cases a <;> cases b <;> simp at h ⊢

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
            intro S _hS
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
            intro S _hS _hmem hfix
            have hmem := congr_arg (fun T : Finset (Fin m) => r ∈ T) hfix
            by_cases hS : r ∈ S <;> simp [finsetToggle, hS] at hmem)
          (by
            intro S _hS
            simp)
          (by
            intro S _hS
            exact finsetToggle_involutive r S))
    simp [hxy, hsum]

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
