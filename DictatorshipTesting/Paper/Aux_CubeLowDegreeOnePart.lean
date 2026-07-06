import DictatorshipTesting.Paper.Aux_CubeHighDegreeLinear
import DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion
import DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality

/-!
# The degree-at-most-one cube truncation
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A cube character of degree at most one has no high-degree Fourier energy. -/
theorem cubeHighDegreeEnergy_cubeChar_eq_zero_of_card_le_one {m : ℕ}
    {S : Finset (Fin m)} (hS : S.card ≤ 1) :
    cubeHighDegreeEnergy (fun x : Cube m => cubeChar S x) = 0 := by
  apply cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero
  intro T hT
  have hne : S ≠ T := by
    intro h
    have : T.card ≤ 1 := by simpa [h] using hS
    omega
  unfold cubeFourierCoeff
  rw [L2_3_cubeChar_orthonormality]
  simp [hne]

/-- Any finite linear combination of degree-at-most-one characters has zero
high-degree Fourier energy. -/
theorem cubeHighDegreeEnergy_sum_low_char_eq_zero {m : ℕ}
    (s : Finset (Finset (Fin m))) (hs : ∀ S ∈ s, S.card ≤ 1)
    (a : Finset (Fin m) → ℝ) :
    cubeHighDegreeEnergy
      (fun x : Cube m => ∑ S ∈ s, a S * cubeChar S x) = 0 := by
  revert hs
  refine Finset.induction_on s ?empty ?insert
  · intro _hs
    apply cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero
    intro S _hS
    unfold cubeFourierCoeff cubeExpectation
    simp
  · intro S s hSnot ih hs
    have hSle : S.card ≤ 1 := hs S (Finset.mem_insert_self S s)
    have hs_tail : ∀ T ∈ s, T.card ≤ 1 := by
      intro T hT
      exact hs T (Finset.mem_insert_of_mem hT)
    simpa [Finset.sum_insert hSnot] using
      cubeHighDegreeEnergy_add_eq_zero
        (cubeHighDegreeEnergy_smul_eq_zero (a S)
          (cubeHighDegreeEnergy_cubeChar_eq_zero_of_card_le_one hSle))
        (ih hs_tail)

/-- The degree-at-most-one truncation has zero high-degree Fourier energy. -/
theorem cubeHighDegreeEnergy_cubeLowDegreeOnePart_eq_zero {m : ℕ}
    (g : Cube m → ℝ) :
    cubeHighDegreeEnergy (cubeLowDegreeOnePart g) = 0 := by
  unfold cubeLowDegreeOnePart
  apply cubeHighDegreeEnergy_sum_low_char_eq_zero
  intro S hS
  exact (Finset.mem_filter.mp hS).2

/-- If all high-degree Fourier coefficients vanish, the degree-at-most-one
truncation is the original function. -/
theorem cubeLowDegreeOnePart_eq_self_of_cubeHighDegreeEnergy_eq_zero {m : ℕ}
    {g : Cube m → ℝ} (hg : cubeHighDegreeEnergy g = 0) :
    cubeLowDegreeOnePart g = g := by
  funext x
  unfold cubeLowDegreeOnePart
  calc
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ 1),
        cubeFourierCoeff g S * cubeChar S x)
        =
        ∑ S : Finset (Fin m),
          if S.card ≤ 1 then cubeFourierCoeff g S * cubeChar S x else 0 := by
          rw [Finset.sum_filter]
    _ =
        ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x := by
          apply Finset.sum_congr rfl
          intro S _
          by_cases hlow : S.card ≤ 1
          · simp [hlow]
          · have hhigh : 2 ≤ S.card := by omega
            have hcoeff :
                cubeFourierCoeff g S = 0 :=
              cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero hg hhigh
            simp [hlow, hcoeff]
    _ = g x := by
          exact (L2_3_cubeFourier_expansion m g x).symm

/-- The degree-at-most-one truncation is idempotent. -/
theorem cubeLowDegreeOnePart_idempotent {m : ℕ} (g : Cube m → ℝ) :
    cubeLowDegreeOnePart (cubeLowDegreeOnePart g) = cubeLowDegreeOnePart g := by
  exact cubeLowDegreeOnePart_eq_self_of_cubeHighDegreeEnergy_eq_zero
    (cubeHighDegreeEnergy_cubeLowDegreeOnePart_eq_zero g)

end DictatorshipTesting
