import DictatorshipTesting.Paper.Aux_CubeLowDegreeOnePart
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity

/-!
# Error of the degree-at-most-one cube projection

The mean-square residual after truncating to Fourier degree at most one is
exactly the high-degree Fourier energy.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Fourier coefficients commute with a finite linear combination of cube
functions. -/
theorem cubeFourierCoeff_sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (φ : ι → Cube m → ℝ) (T : Finset (Fin m)) :
    cubeFourierCoeff (fun x : Cube m => ∑ i ∈ s, a i * φ i x) T =
      ∑ i ∈ s, a i * cubeFourierCoeff (φ i) T := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · unfold cubeFourierCoeff cubeExpectation
    simp
  · intro i s his ih
    simp [Finset.sum_insert his, cubeFourierCoeff_add,
      cubeFourierCoeff_smul, ih]

/-- Fourier coefficient of a cube character. -/
theorem cubeFourierCoeff_cubeChar {m : ℕ} (S T : Finset (Fin m)) :
    cubeFourierCoeff (fun x : Cube m => cubeChar S x) T =
      if S = T then 1 else 0 := by
  unfold cubeFourierCoeff
  rw [L2_3_cubeChar_orthonormality]

/-- The degree-at-most-one part preserves exactly the coefficients of degree at
most one. -/
theorem cubeFourierCoeff_cubeLowDegreeOnePart {m : ℕ}
    (g : Cube m → ℝ) (T : Finset (Fin m)) :
    cubeFourierCoeff (cubeLowDegreeOnePart g) T =
      if T.card ≤ 1 then cubeFourierCoeff g T else 0 := by
  classical
  unfold cubeLowDegreeOnePart
  rw [cubeFourierCoeff_sum]
  by_cases hT : T.card ≤ 1
  · rw [if_pos hT]
    rw [Finset.sum_eq_single T]
    · simp [cubeFourierCoeff_cubeChar]
    · intro S hS hne
      simp [cubeFourierCoeff_cubeChar, hne]
    · intro hTnot
      exact False.elim (hTnot (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩))
  · rw [if_neg hT]
    apply Finset.sum_eq_zero
    intro S hS
    have hne : S ≠ T := by
      intro h
      have hSle : S.card ≤ 1 := (Finset.mem_filter.mp hS).2
      exact hT (by simpa [h] using hSle)
    simp [cubeFourierCoeff_cubeChar, hne]

/-- Fourier coefficients are additive inverses under negation of the function. -/
theorem cubeFourierCoeff_neg {m : ℕ} (g : Cube m → ℝ)
    (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => -g x) S = -cubeFourierCoeff g S := by
  simpa using cubeFourierCoeff_smul (-1 : ℝ) g S

/-- Fourier coefficients commute with subtraction of cube functions. -/
theorem cubeFourierCoeff_sub {m : ℕ} (g h : Cube m → ℝ)
    (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => g x - h x) S =
      cubeFourierCoeff g S - cubeFourierCoeff h S := by
  calc
    cubeFourierCoeff (fun x => g x - h x) S =
        cubeFourierCoeff (fun x => g x + -h x) S := by
          rfl
    _ = cubeFourierCoeff g S + cubeFourierCoeff (fun x => -h x) S := by
          rw [cubeFourierCoeff_add]
    _ = cubeFourierCoeff g S - cubeFourierCoeff h S := by
          rw [cubeFourierCoeff_neg]
          ring

/-- The residual after degree-at-most-one truncation has exactly the high-degree
Fourier coefficients of the original function. -/
theorem cubeFourierCoeff_lowDegreeResidual {m : ℕ}
    (g : Cube m → ℝ) (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => g x - cubeLowDegreeOnePart g x) S =
      if 2 ≤ S.card then cubeFourierCoeff g S else 0 := by
  rw [cubeFourierCoeff_sub, cubeFourierCoeff_cubeLowDegreeOnePart]
  by_cases hlow : S.card ≤ 1
  · have hhigh : ¬ 2 ≤ S.card := by omega
    simp [hlow, hhigh]
  · have hhigh : 2 ≤ S.card := by omega
    simp [hlow, hhigh]

/-- Parseval for the residual of the degree-at-most-one cube truncation. -/
theorem cubeExpectation_sq_sub_cubeLowDegreeOnePart_eq_highDegreeEnergy
    {m : ℕ} (g : Cube m → ℝ) :
    cubeExpectation
        (fun x : Cube m => (g x - cubeLowDegreeOnePart g x) ^ (2 : ℕ)) =
      cubeHighDegreeEnergy g := by
  rw [L2_3_cubeParseval_identity]
  unfold cubeHighDegreeEnergy
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _hS
  by_cases hS : 2 ≤ S.card
  · simp [cubeFourierCoeff_lowDegreeResidual, hS]
  · simp [cubeFourierCoeff_lowDegreeResidual, hS]

end DictatorshipTesting
