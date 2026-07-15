import AlgebraicLibrary.BooleanCube.LowDegree

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError`
- `DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare`
- `DictatorshipTesting.Paper.S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne`
-/
/-!
# Linearity of high-degree cube Fourier support
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- FinCube Fourier coefficients are additive in the function. -/
theorem cubeFourierCoeff_add {m : ℕ} (g h : FinCube m → ℝ)
    (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => g x + h x) S =
      cubeFourierCoeff g S + cubeFourierCoeff h S := by
  unfold cubeFourierCoeff cubeExpectation
  calc
    (∑ x : FinCube m, (g x + h x) * cubeChar S x) /
        (Fintype.card (FinCube m) : ℝ)
        =
        (∑ x : FinCube m, (g x * cubeChar S x + h x * cubeChar S x)) /
          (Fintype.card (FinCube m) : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ =
        ((∑ x : FinCube m, g x * cubeChar S x) +
          (∑ x : FinCube m, h x * cubeChar S x)) /
          (Fintype.card (FinCube m) : ℝ) := by
          rw [Finset.sum_add_distrib]
    _ =
        (∑ x : FinCube m, g x * cubeChar S x) /
            (Fintype.card (FinCube m) : ℝ) +
          (∑ x : FinCube m, h x * cubeChar S x) /
            (Fintype.card (FinCube m) : ℝ) := by
          rw [add_div]

/-- FinCube Fourier coefficients are homogeneous in the function. -/
theorem cubeFourierCoeff_smul {m : ℕ} (a : ℝ) (g : FinCube m → ℝ)
    (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => a * g x) S =
      a * cubeFourierCoeff g S := by
  unfold cubeFourierCoeff cubeExpectation
  calc
    (∑ x : FinCube m, (a * g x) * cubeChar S x) /
        (Fintype.card (FinCube m) : ℝ)
        =
        (a * ∑ x : FinCube m, g x * cubeChar S x) /
          (Fintype.card (FinCube m) : ℝ) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ =
        a * ((∑ x : FinCube m, g x * cubeChar S x) /
          (Fintype.card (FinCube m) : ℝ)) := by
          ring

/-- If the high-degree energy is zero, each high-degree coefficient is zero. -/
theorem cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero {m : ℕ}
    {g : FinCube m → ℝ} (hE : cubeHighDegreeEnergy g = 0)
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) :
    cubeFourierCoeff g S = 0 := by
  classical
  unfold cubeHighDegreeEnergy at hE
  have hterm :
      (cubeFourierCoeff g S) ^ (2 : ℕ) = 0 := by
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ.filter (fun T : Finset (Fin m) => 2 ≤ T.card))
        (f := fun T => (cubeFourierCoeff g T) ^ (2 : ℕ))
        (by
          intro T _hT
          exact sq_nonneg (cubeFourierCoeff g T))).mp hE
    exact hzero S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)
  exact sq_eq_zero_iff.mp hterm

/-- Vanishing of all high-degree coefficients implies vanishing high-degree energy. -/
theorem cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero {m : ℕ}
    {g : FinCube m → ℝ}
    (hcoeff : ∀ S : Finset (Fin m), 2 ≤ S.card → cubeFourierCoeff g S = 0) :
    cubeHighDegreeEnergy g = 0 := by
  classical
  unfold cubeHighDegreeEnergy
  apply Finset.sum_eq_zero
  intro S hS
  have hcard : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
  simp [hcoeff S hcard]

/-- High-degree-energy zero is closed under addition. -/
theorem cubeHighDegreeEnergy_add_eq_zero {m : ℕ} {g h : FinCube m → ℝ}
    (hg : cubeHighDegreeEnergy g = 0) (hh : cubeHighDegreeEnergy h = 0) :
    cubeHighDegreeEnergy (fun x => g x + h x) = 0 := by
  apply cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero
  intro S hS
  rw [cubeFourierCoeff_add]
  rw [cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero hg hS,
    cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero hh hS]
  ring

/-- High-degree-energy zero is closed under scalar multiplication. -/
theorem cubeHighDegreeEnergy_smul_eq_zero {m : ℕ} (a : ℝ) {g : FinCube m → ℝ}
    (hg : cubeHighDegreeEnergy g = 0) :
    cubeHighDegreeEnergy (fun x => a * g x) = 0 := by
  apply cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero
  intro S hS
  rw [cubeFourierCoeff_smul]
  rw [cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero hg hS]
  ring

end DictatorshipTesting
