import DictatorshipTesting.Paper.Aux_PMConvolutionLegacy

/-!
Paper statement: Lemma 5.23 (`lem:PM-convolution`)
Title in paper: Local truncation as convolution.

Status: paper-facing wrapper around the existing local-projection convolution
identity.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.23: local projection as low-degree convolution, with residual equal
to high-degree convolution. -/
theorem S05_Lem5_23_local_truncation_as_convolution
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    matchingLocalProjection M F = matchingLowConvolution M F ∧
      (fun π => F π - matchingLocalProjection M F π) =
        matchingHighConvolution M F := by
  exact L5_1_PMConvolution M F

end DictatorshipTesting
