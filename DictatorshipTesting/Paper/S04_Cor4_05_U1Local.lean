import DictatorshipTesting.Paper.S04_Int_CubeHighDegreeLinear
import DictatorshipTesting.Paper.S04_Prop4_03_MatchingLocalTruncationOrthogonalProjection
import DictatorshipTesting.Paper.S04_Lem4_04_TijLocalDegree

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
-/


/-!
# Corollary 4.5: `U_1` is contained in every local degree-one space

This is `cor:U1-local` from `dictatorship_testing_stoc27_latest.tex`.
-/

namespace DictatorshipTesting

/-- The zero cube function has no high-degree Fourier energy. -/
theorem cubeHighDegreeEnergy_zero (m : ℕ) :
    cubeHighDegreeEnergy (fun _ : Cube m => (0 : ℝ)) = 0 := by
  apply cubeHighDegreeEnergy_eq_zero_of_forall_highDegree_coeff_zero
  intro S _hS
  unfold cubeFourierCoeff cubeExpectation
  simp

/-- The zero function is matching-local degree one. -/
theorem IsMatchingLocalDegreeOne_zero {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) :
    IsMatchingLocalDegreeOne (fun _ : Perm α => (0 : ℝ)) M := by
  intro π
  simpa using cubeHighDegreeEnergy_zero M.edgeCount

/-- Matching-local degree one is closed under addition. -/
theorem IsMatchingLocalDegreeOne_add {α : Type*} [Fintype α] [DecidableEq α]
    {F G : Perm α → ℝ} {M : OrderedMatching α}
    (hF : IsMatchingLocalDegreeOne F M)
    (hG : IsMatchingLocalDegreeOne G M) :
    IsMatchingLocalDegreeOne (F + G) M := by
  intro π
  simpa [Pi.add_apply] using cubeHighDegreeEnergy_add_eq_zero (hF π) (hG π)

/-- Matching-local degree one is closed under scalar multiplication. -/
theorem IsMatchingLocalDegreeOne_smul {α : Type*} [Fintype α] [DecidableEq α]
    (a : ℝ) {F : Perm α → ℝ} {M : OrderedMatching α}
    (hF : IsMatchingLocalDegreeOne F M) :
    IsMatchingLocalDegreeOne (a • F) M := by
  intro π
  simpa [Pi.smul_apply, smul_eq_mul] using
    cubeHighDegreeEnergy_smul_eq_zero a (hF π)

/-- Corollary 4.5, `cor:U1-local`: `U_1` is contained in each local degree-one space. -/
theorem S04_Cor4_05_U1Local {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) (hF : F ∈ U1 α) :
    IsMatchingLocalDegreeOne F M ∧ matchingLocalProjection M F = F := by
  have hlocal : IsMatchingLocalDegreeOne F M := by
    unfold U1 at hF
    refine Submodule.span_induction
      (p := fun F _ => IsMatchingLocalDegreeOne F M)
      ?mem ?zero ?add ?smul hF
    · intro G hG
      rcases hG with ⟨ij, rfl⟩
      exact S04_Lem4_04_TijLocalDegree M ij.1 ij.2
    · exact IsMatchingLocalDegreeOne_zero M
    · intro G H _hGmem _hHmem hG hH
      exact IsMatchingLocalDegreeOne_add hG hH
    · intro a G _hGmem hG
      exact IsMatchingLocalDegreeOne_smul a hG
  exact ⟨hlocal, (S04_Prop4_03_fixedSpace F M).2 F hlocal⟩

end DictatorshipTesting
