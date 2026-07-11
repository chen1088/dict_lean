import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeExpectation
import DictatorshipTesting.Paper.S02_Int_CubeCharFlip
import DictatorshipTesting.Paper.S02_Int_CubeCharMulSelf
import DictatorshipTesting.Paper.S02_Int_CubeFlipInvolutive

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval`
- `DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError`
-/


/-!
# Lemma 2.3: cube-character orthonormality

This proves the first displayed identity in `lem:cube-parseval`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Flipping a coordinate outside the character support leaves that character unchanged. -/
theorem cubeChar_cubeFlip_of_not_mem {m : ℕ} (S : Finset (Fin m)) (r : Fin m)
    (hr : r ∉ S) (x : Cube m) :
    cubeChar S (cubeFlip r x) = cubeChar S x := by
  unfold cubeChar
  apply Finset.prod_congr rfl
  intro q hq
  have hqr : q ≠ r := by
    intro h
    exact hr (h ▸ hq)
  simp [cubeFlip, hqr]

/-- The orthonormality part of Lemma 2.3, `lem:cube-parseval`. -/
theorem S02_Lem2_03_cubeChar_orthonormality (m : ℕ) :
    ∀ S T : Finset (Fin m),
      cubeExpectation (fun x : Cube m => cubeChar S x * cubeChar T x) =
        if S = T then 1 else 0 := by
  intro S T
  classical
  by_cases hST : S = T
  · subst T
    have hsum :
        (∑ x : Cube m, cubeChar S x * cubeChar S x) =
          (Fintype.card (Cube m) : ℝ) := by
      simp [cubeChar_mul_self]
    simp [cubeExpectation, hsum]
  · have hex :
        ∃ r : Fin m, (r ∈ S ∧ r ∉ T) ∨ (r ∈ T ∧ r ∉ S) := by
      by_contra h
      apply hST
      ext r
      have hr := not_exists.mp h r
      constructor
      · intro hrS
        by_contra hrT
        exact hr (Or.inl ⟨hrS, hrT⟩)
      · intro hrT
        by_contra hrS
        exact hr (Or.inr ⟨hrT, hrS⟩)
    rcases hex with ⟨r, hmem | hmem⟩
    · rcases hmem with ⟨hrS, hrT⟩
      have hsum :
          (∑ x : Cube m, cubeChar S x * cubeChar T x) = 0 := by
        simpa using
          (Finset.sum_involution
            (s := (Finset.univ : Finset (Cube m)))
            (f := fun x => cubeChar S x * cubeChar T x)
            (g := fun x _ => cubeFlip r x)
            (by
              intro x _
              rw [cubeChar_cubeFlip S r hrS x,
                cubeChar_cubeFlip_of_not_mem T r hrT x]
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
      simp [cubeExpectation, hsum, hST]
    · rcases hmem with ⟨hrT, hrS⟩
      have hsum :
          (∑ x : Cube m, cubeChar S x * cubeChar T x) = 0 := by
        simpa using
          (Finset.sum_involution
            (s := (Finset.univ : Finset (Cube m)))
            (f := fun x => cubeChar S x * cubeChar T x)
            (g := fun x _ => cubeFlip r x)
            (by
              intro x _
              rw [cubeChar_cubeFlip_of_not_mem S r hrS x,
                cubeChar_cubeFlip T r hrT x]
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
      simp [cubeExpectation, hsum, hST]

end DictatorshipTesting
