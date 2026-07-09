import DictatorshipTesting.Paper.Defs.S03_Def3_25_OneTrialRejectProbability

/-!
Definition file for `matchingLowConvolution`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Low-character convolution side of the local projection formula.

This is the sum of the matching-cube Fourier idempotents indexed by characters
of support size at most one, evaluated on the matching cube based at `π`. -/
def matchingLowConvolution {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin M.edgeCount) => S.card ≤ 1)),
      cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
        cubeChar S (cubeZero M.edgeCount)

end DictatorshipTesting
