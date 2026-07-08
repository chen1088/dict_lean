import DictatorshipTesting.Paper.Aux_CubeHighDegreeLinear
import DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion
import DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity

/-!
# Error of the degree-at-most-one cube projection

The mean-square residual after truncating to Fourier degree at most one is
exactly the high-degree Fourier energy.
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
          intro S _hS
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

/-- The degree-at-most-one truncation kills its own residual. -/
theorem cubeLowDegreeOnePart_lowDegreeResidual_eq_zero {m : ℕ}
    (g : Cube m → ℝ) :
    cubeLowDegreeOnePart (fun x => g x - cubeLowDegreeOnePart g x) =
      fun _ => 0 := by
  classical
  funext x
  unfold cubeLowDegreeOnePart
  apply Finset.sum_eq_zero
  intro S hS
  have hlow : S.card ≤ 1 := (Finset.mem_filter.mp hS).2
  have hnotHigh : ¬ 2 ≤ S.card := by omega
  have hcoeff :
      cubeFourierCoeff (fun x => g x - cubeLowDegreeOnePart g x) S = 0 := by
    simpa [hnotHigh] using cubeFourierCoeff_lowDegreeResidual g S
  have hcoeff' :
      cubeFourierCoeff
          (fun x => g x -
            ∑ S with S.card ≤ 1, cubeFourierCoeff g S * cubeChar S x) S = 0 := by
    simpa [cubeLowDegreeOnePart] using hcoeff
  rw [hcoeff']
  ring

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
