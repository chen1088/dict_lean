import AlgebraicLibrary.BooleanCube.Basic

/-!
# Walsh--Fourier analysis on Boolean cubes

Real Walsh characters, uniform expectation, Fourier coefficients,
orthonormality, inversion, Parseval, and translation.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- A real Walsh character indexed by a finite set of coordinates. -/
def cubeChar {ι : Type*} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, if x i then (-1 : ℝ) else 1

/-- Uniform expectation on a finite Boolean cube. -/
def cubeExpectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) : ℝ :=
  (∑ x : Cube ι, g x) / (Fintype.card (Cube ι) : ℝ)

/-- Fourier coefficient of a real-valued Boolean-cube function. -/
def cubeFourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) (S : Finset ι) : ℝ :=
  cubeExpectation fun x => g x * cubeChar S x

/-- The `{1,-1}` sign of xor is the product of signs. -/
theorem boolSign_xor (a b : Bool) :
    (if a ^^ b then (-1 : ℝ) else 1) =
      (if a then (-1 : ℝ) else 1) * (if b then (-1 : ℝ) else 1) := by
  cases a <;> cases b <;> simp

/-- Walsh characters multiply under coordinatewise xor. -/
theorem cubeChar_cubeXor {ι : Type*} (S : Finset ι) (x y : Cube ι) :
    cubeChar S (cubeXor x y) = cubeChar S x * cubeChar S y := by
  unfold cubeChar cubeXor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  exact boolSign_xor (x i) (y i)

/-- A Walsh character squares to one. -/
@[simp] theorem cubeChar_mul_self {ι : Type*} (S : Finset ι) (x : Cube ι) :
    cubeChar S x * cubeChar S x = 1 := by
  unfold cubeChar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _hi
  by_cases hx : x i <;> simp [hx]

/-- Flipping a coordinate in the character support negates that character. -/
theorem cubeChar_cubeFlip {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (i : ι) (hi : i ∈ S) (x : Cube ι) :
    cubeChar S (cubeFlip i x) = -cubeChar S x := by
  unfold cubeChar
  rw [← Finset.mul_prod_erase S
    (fun j => if cubeFlip i x j then (-1 : ℝ) else 1) (a := i) hi]
  rw [← Finset.mul_prod_erase S
    (fun j => if x j then (-1 : ℝ) else 1) (a := i) hi]
  have hprod :
      (∏ j ∈ S.erase i, if cubeFlip i x j then (-1 : ℝ) else 1) =
        ∏ j ∈ S.erase i, if x j then (-1 : ℝ) else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [cubeFlip, hji]
  rw [hprod]
  by_cases hx : x i <;> simp [cubeFlip, hx]

/-- Flipping a coordinate outside the character support leaves it unchanged. -/
theorem cubeChar_cubeFlip_of_not_mem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (i : ι) (hi : i ∉ S) (x : Cube ι) :
    cubeChar S (cubeFlip i x) = cubeChar S x := by
  unfold cubeChar
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    exact hi (h ▸ hj)
  simp [cubeFlip, hji]

/-- Toggle membership of one element in a finset. -/
def finsetToggle {α : Type*} [DecidableEq α] (a : α) (S : Finset α) : Finset α :=
  if a ∈ S then S.erase a else insert a S

/-- Toggling the same finset element twice is the identity. -/
@[simp] theorem finsetToggle_involutive {α : Type*} [DecidableEq α]
    (a : α) (S : Finset α) : finsetToggle a (finsetToggle a S) = S := by
  by_cases h : a ∈ S <;> simp [finsetToggle, h]

/-- Toggling a character support multiplies the character by one coordinate sign. -/
theorem cubeChar_finsetToggle {ι : Type*} [DecidableEq ι]
    (i : ι) (S : Finset ι) (x : Cube ι) :
    cubeChar (finsetToggle i S) x =
      (if x i then (-1 : ℝ) else 1) * cubeChar S x := by
  unfold cubeChar
  by_cases hi : i ∈ S
  · rw [show finsetToggle i S = S.erase i by simp [finsetToggle, hi]]
    rw [← Finset.mul_prod_erase S (fun j => if x j then (-1 : ℝ) else 1) (a := i) hi]
    by_cases hx : x i <;> simp [hx]
  · rw [show finsetToggle i S = insert i S by simp [finsetToggle, hi]]
    rw [Finset.prod_insert hi]

/-- Distinct Boolean bits have opposite `{1,-1}` signs. -/
theorem boolSign_mul_eq_neg_one_of_ne {a b : Bool} (h : a ≠ b) :
    ((if a then (-1 : ℝ) else 1) * (if b then (-1 : ℝ) else 1)) = -1 := by
  cases a <;> cases b <;> simp at h ⊢

/-- Walsh characters are orthonormal for uniform expectation. -/
theorem cubeChar_orthonormality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) :
    cubeExpectation (fun x : Cube ι => cubeChar S x * cubeChar T x) =
      if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T
    simp [cubeExpectation, cubeChar_mul_self]
  · have hex : ∃ i : ι, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra h
      apply hST
      ext i
      have hi := not_exists.mp h i
      constructor
      · intro hiS
        by_contra hiT
        exact hi (Or.inl ⟨hiS, hiT⟩)
      · intro hiT
        by_contra hiS
        exact hi (Or.inr ⟨hiT, hiS⟩)
    rcases hex with ⟨i, hmem | hmem⟩
    · rcases hmem with ⟨hiS, hiT⟩
      have hsum : (∑ x : Cube ι, cubeChar S x * cubeChar T x) = 0 := by
        simpa using
          (Finset.sum_involution
            (s := (Finset.univ : Finset (Cube ι)))
            (f := fun x => cubeChar S x * cubeChar T x)
            (g := fun x _ => cubeFlip i x)
            (by
              intro x _
              rw [cubeChar_cubeFlip S i hiS x,
                cubeChar_cubeFlip_of_not_mem T i hiT x]
              ring)
            (by
              intro x _ _ hfix
              have hcoord := congr_fun hfix i
              by_cases hx : x i <;> simp [cubeFlip, hx] at hcoord)
            (by intro x _; simp)
            (by intro x _; exact cubeFlip_involutive i x))
      simp [cubeExpectation, hsum, hST]
    · rcases hmem with ⟨hiT, hiS⟩
      have hsum : (∑ x : Cube ι, cubeChar S x * cubeChar T x) = 0 := by
        simpa using
          (Finset.sum_involution
            (s := (Finset.univ : Finset (Cube ι)))
            (f := fun x => cubeChar S x * cubeChar T x)
            (g := fun x _ => cubeFlip i x)
            (by
              intro x _
              rw [cubeChar_cubeFlip_of_not_mem S i hiS x,
                cubeChar_cubeFlip T i hiT x]
              ring)
            (by
              intro x _ _ hfix
              have hcoord := congr_fun hfix i
              by_cases hx : x i <;> simp [cubeFlip, hx] at hcoord)
            (by intro x _; simp)
            (by intro x _; exact cubeFlip_involutive i x))
      simp [cubeExpectation, hsum, hST]

/-- Dual orthogonality, summing over all character supports. -/
theorem cubeChar_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : Cube ι) :
    (∑ S : Finset ι, cubeChar S y * cubeChar S x) =
      if x = y then (Fintype.card (Cube ι) : ℝ) else 0 := by
  classical
  by_cases hxy : x = y
  · rw [if_pos hxy]
    subst y
    have hcard : Fintype.card (Finset ι) = Fintype.card (Cube ι) := by
      simp [Cube, BooleanCube, Fintype.card_finset]
    calc
      (∑ S : Finset ι, cubeChar S x * cubeChar S x) =
          ∑ _S : Finset ι, (1 : ℝ) := by simp [cubeChar_mul_self]
      _ = (Fintype.card (Finset ι) : ℝ) := by simp
      _ = (Fintype.card (Cube ι) : ℝ) := by exact_mod_cast hcard
  · have hex : ∃ i : ι, x i ≠ y i := by
      by_contra h
      apply hxy
      ext i
      exact not_not.mp (not_exists.mp h i)
    rcases hex with ⟨i, hi⟩
    have hsum : (∑ S : Finset ι, cubeChar S y * cubeChar S x) = 0 := by
      simpa using
        (Finset.sum_involution
          (s := (Finset.univ : Finset (Finset ι)))
          (f := fun S => cubeChar S y * cubeChar S x)
          (g := fun S _ => finsetToggle i S)
          (by
            intro S _hS
            rw [cubeChar_finsetToggle i S y, cubeChar_finsetToggle i S x]
            have hsign : ((if y i then (-1 : ℝ) else 1) *
                (if x i then (-1 : ℝ) else 1)) = -1 :=
              boolSign_mul_eq_neg_one_of_ne (fun h => hi h.symm)
            calc
              cubeChar S y * cubeChar S x +
                  (if y i then (-1 : ℝ) else 1) * cubeChar S y *
                    ((if x i then (-1 : ℝ) else 1) * cubeChar S x) =
                  cubeChar S y * cubeChar S x +
                    (((if y i then (-1 : ℝ) else 1) *
                      (if x i then (-1 : ℝ) else 1)) *
                      (cubeChar S y * cubeChar S x)) := by ring
              _ = 0 := by rw [hsign]; ring)
          (by
            intro S _hS _hmem hfix
            have hmem := congr_arg (fun T : Finset ι => i ∈ T) hfix
            by_cases hS : i ∈ S <;> simp [finsetToggle, hS] at hmem)
          (by intro S _hS; simp)
          (by intro S _hS; exact finsetToggle_involutive i S))
    simp [hxy, hsum]

/-- Fourier inversion on a finite Boolean cube. -/
theorem cubeFourier_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) (x : Cube ι) :
    g x = ∑ S : Finset ι, cubeFourierCoeff g S * cubeChar S x := by
  classical
  let N : ℝ := Fintype.card (Cube ι)
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast Fintype.card_ne_zero
  symm
  calc
    ∑ S : Finset ι, cubeFourierCoeff g S * cubeChar S x =
        (∑ y : Cube ι, g y *
          (∑ S : Finset ι, cubeChar S y * cubeChar S x)) / N := by
      calc
        ∑ S : Finset ι, cubeFourierCoeff g S * cubeChar S x =
            ∑ S : Finset ι,
              (((∑ y : Cube ι, g y * cubeChar S y) / N) * cubeChar S x) := by
                simp [cubeFourierCoeff, cubeExpectation, N]
        _ = ∑ S : Finset ι,
              ∑ y : Cube ι, (g y * cubeChar S y * cubeChar S x) / N := by
                apply Finset.sum_congr rfl
                intro S _
                rw [← Finset.sum_div, div_mul_eq_mul_div, Finset.sum_mul]
        _ = ∑ y : Cube ι,
              ∑ S : Finset ι, (g y * cubeChar S y * cubeChar S x) / N :=
                Finset.sum_comm
        _ = ∑ y : Cube ι,
              (g y * (∑ S : Finset ι, cubeChar S y * cubeChar S x)) / N := by
                apply Finset.sum_congr rfl
                intro y _
                rw [← Finset.sum_div]
                simp [Finset.mul_sum, mul_left_comm, mul_comm]
        _ = (∑ y : Cube ι, g y *
              (∑ S : Finset ι, cubeChar S y * cubeChar S x)) / N := by
                rw [Finset.sum_div]
    _ = (∑ y : Cube ι, g y * (if x = y then N else 0)) / N := by
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
    _ = g x := by field_simp [hN]

/-- Parseval's identity on a finite Boolean cube. -/
theorem cubeParseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) :
    cubeExpectation (fun x : Cube ι => g x ^ (2 : ℕ)) =
      ∑ S : Finset ι, (cubeFourierCoeff g S) ^ (2 : ℕ) := by
  classical
  let N : ℝ := Fintype.card (Cube ι)
  calc
    cubeExpectation (fun x : Cube ι => g x ^ (2 : ℕ)) =
        cubeExpectation
          (fun x : Cube ι =>
            g x * (∑ S : Finset ι, cubeFourierCoeff g S * cubeChar S x)) := by
      congr
      ext x
      rw [← cubeFourier_expansion g x]
      ring
    _ = ∑ S : Finset ι, cubeFourierCoeff g S *
          cubeExpectation (fun x : Cube ι => g x * cubeChar S x) := by
      calc
        cubeExpectation
            (fun x : Cube ι =>
              g x * (∑ S : Finset ι, cubeFourierCoeff g S * cubeChar S x)) =
            (∑ x : Cube ι,
              g x * (∑ S : Finset ι, cubeFourierCoeff g S * cubeChar S x)) / N := by
                simp [cubeExpectation, N]
        _ = (∑ x : Cube ι,
              ∑ S : Finset ι,
                g x * (cubeFourierCoeff g S * cubeChar S x)) / N := by
                congr 1
                apply Finset.sum_congr rfl
                intro x _
                rw [Finset.mul_sum]
        _ = (∑ S : Finset ι,
              ∑ x : Cube ι,
                g x * (cubeFourierCoeff g S * cubeChar S x)) / N := by
                rw [Finset.sum_comm]
        _ = ∑ S : Finset ι,
              (∑ x : Cube ι,
                g x * (cubeFourierCoeff g S * cubeChar S x)) / N := by
                rw [Finset.sum_div]
        _ = ∑ S : Finset ι, cubeFourierCoeff g S *
              cubeExpectation (fun x : Cube ι => g x * cubeChar S x) := by
                apply Finset.sum_congr rfl
                intro S _
                unfold cubeExpectation
                calc
                  (∑ x : Cube ι,
                      g x * (cubeFourierCoeff g S * cubeChar S x)) / N =
                      (cubeFourierCoeff g S *
                        (∑ x : Cube ι, g x * cubeChar S x)) / N := by
                          congr 1
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro x _
                          ring
                  _ = cubeFourierCoeff g S *
                        ((∑ x : Cube ι, g x * cubeChar S x) / N) := by ring
                  _ = cubeFourierCoeff g S *
                        ((∑ x : Cube ι, g x * cubeChar S x) /
                          (Fintype.card (Cube ι) : ℝ)) := by simp [N]
    _ = ∑ S : Finset ι, (cubeFourierCoeff g S) ^ (2 : ℕ) := by
      simp [cubeFourierCoeff, pow_two]

/-- Translation by xor multiplies Fourier coefficients by a character value. -/
theorem cubeFourierCoeff_xor_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → ℝ) (z : Cube ι) (S : Finset ι) :
    cubeFourierCoeff (fun y => g (cubeXor z y)) S =
      cubeChar S z * cubeFourierCoeff g S := by
  unfold cubeFourierCoeff cubeExpectation
  have hchange :
      (∑ y : Cube ι, g (cubeXor z y) * cubeChar S y) =
        ∑ t : Cube ι, g t * cubeChar S (cubeXor z t) := by
    refine Fintype.sum_equiv (cubeXorEquiv z)
      (fun y : Cube ι => g (cubeXor z y) * cubeChar S y)
      (fun t : Cube ι => g t * cubeChar S (cubeXor z t)) ?_
    intro y
    simp [cubeXorEquiv, cubeXor_self_left]
  have hfactor :
      (∑ t : Cube ι, g t * cubeChar S (cubeXor z t)) =
        cubeChar S z * (∑ t : Cube ι, g t * cubeChar S t) := by
    calc
      (∑ t : Cube ι, g t * cubeChar S (cubeXor z t)) =
          ∑ t : Cube ι, g t * (cubeChar S z * cubeChar S t) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [cubeChar_cubeXor]
      _ = cubeChar S z * (∑ t : Cube ι, g t * cubeChar S t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
  rw [hchange, hfactor]
  ring

end AlgebraicLibrary
