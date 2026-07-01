import DictatorshipTesting.Paper.Aux_CubeHighDegreeLinear

/-!
# Linearity of matching-local degree one
-/

noncomputable section

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

end DictatorshipTesting
