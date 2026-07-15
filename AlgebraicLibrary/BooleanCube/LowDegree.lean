import AlgebraicLibrary.BooleanCube.Fourier

/-! Fourier truncations and high-degree energy on finite Boolean cubes. -/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- Fourier projection onto characters of degree at most `d`. -/
def cubeLowDegreePart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (g : Cube ι → ℝ) : Cube ι → ℝ :=
  fun x =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset ι => S.card ≤ d)),
      cubeFourierCoeff g S * cubeChar S x

/-- Backwards-compatible name for the degree-at-most-one projection. -/
def cubeLowDegreeOnePart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) : Cube ι → ℝ :=
  fun x =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset ι => S.card ≤ 1)),
      cubeFourierCoeff g S * cubeChar S x

/-- Fourier energy in degrees strictly larger than `d`. -/
def cubeHighDegreeEnergyAbove {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (g : Cube ι → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun S : Finset ι => d < S.card)),
    (cubeFourierCoeff g S) ^ (2 : ℕ)

/-- Fourier energy in degrees at least two. -/
def cubeHighDegreeEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun S : Finset ι => 2 ≤ S.card)),
    (cubeFourierCoeff g S) ^ (2 : ℕ)

theorem cubeFourierCoeff_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g h : Cube ι → ℝ) (S : Finset ι) :
    cubeFourierCoeff (fun x => g x + h x) S =
      cubeFourierCoeff g S + cubeFourierCoeff h S := by
  unfold cubeFourierCoeff cubeExpectation
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem cubeFourierCoeff_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (g : Cube ι → ℝ) (S : Finset ι) :
    cubeFourierCoeff (fun x => a * g x) S = a * cubeFourierCoeff g S := by
  unfold cubeFourierCoeff cubeExpectation
  calc
    (∑ x : Cube ι, (a * g x) * cubeChar S x) /
        (Fintype.card (Cube ι) : ℝ)
        =
        (a * ∑ x : Cube ι, g x * cubeChar S x) /
          (Fintype.card (Cube ι) : ℝ) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ =
        a * ((∑ x : Cube ι, g x * cubeChar S x) /
          (Fintype.card (Cube ι) : ℝ)) := by
            ring

theorem cubeFourierCoeff_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) (S : Finset ι) :
    cubeFourierCoeff (fun x => -g x) S = -cubeFourierCoeff g S := by
  simpa using cubeFourierCoeff_smul (-1) g S

theorem cubeFourierCoeff_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g h : Cube ι → ℝ) (S : Finset ι) :
    cubeFourierCoeff (fun x => g x - h x) S =
      cubeFourierCoeff g S - cubeFourierCoeff h S := by
  simpa [sub_eq_add_neg, cubeFourierCoeff_neg] using
    cubeFourierCoeff_add g (fun x => -h x) S

theorem cubeFourierCoeff_cubeChar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) :
    cubeFourierCoeff (cubeChar S) T = if S = T then 1 else 0 := by
  unfold cubeFourierCoeff
  simpa [mul_comm] using cubeChar_orthonormality S T

theorem cubeFourierCoeff_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset κ) (f : κ → Cube ι → ℝ) (S : Finset ι) :
    cubeFourierCoeff (fun x => ∑ k ∈ s, f k x) S =
      ∑ k ∈ s, cubeFourierCoeff (f k) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubeFourierCoeff, cubeExpectation]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [cubeFourierCoeff_add, ih]

theorem cubeFourierCoeff_cubeLowDegreePart {ι : Type*}
    [Fintype ι] [DecidableEq ι] (d : ℕ) (g : Cube ι → ℝ) (T : Finset ι) :
    cubeFourierCoeff (cubeLowDegreePart d g) T =
      if T.card ≤ d then cubeFourierCoeff g T else 0 := by
  classical
  unfold cubeLowDegreePart
  rw [cubeFourierCoeff_sum]
  simp only [cubeFourierCoeff_smul, cubeFourierCoeff_cubeChar]
  by_cases hT : T.card ≤ d
  · rw [if_pos hT]
    rw [Finset.sum_eq_single T]
    · simp
    · intro S hS hST
      simp [hST]
    · intro hTmem
      exact (hTmem (by simp [hT])).elim
  · rw [if_neg hT]
    apply Finset.sum_eq_zero
    intro S hS
    have hSne : S ≠ T := by
      intro h
      subst S
      exact hT (by simpa using (Finset.mem_filter.mp hS).2)
    simp [hSne]

theorem cubeLowDegreePart_idempotent {ι : Type*}
    [Fintype ι] [DecidableEq ι] (d : ℕ) (g : Cube ι → ℝ) :
    cubeLowDegreePart d (cubeLowDegreePart d g) = cubeLowDegreePart d g := by
  funext x
  change
    (∑ S ∈ (Finset.univ.filter (fun S : Finset ι => S.card ≤ d)),
        cubeFourierCoeff (cubeLowDegreePart d g) S * cubeChar S x) =
      ∑ S ∈ (Finset.univ.filter (fun S : Finset ι => S.card ≤ d)),
        cubeFourierCoeff g S * cubeChar S x
  apply Finset.sum_congr rfl
  intro S hS
  have hcard : S.card ≤ d := (Finset.mem_filter.mp hS).2
  rw [cubeFourierCoeff_cubeLowDegreePart, if_pos hcard]

end AlgebraicLibrary
