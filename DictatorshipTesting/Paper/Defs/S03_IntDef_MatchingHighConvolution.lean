import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingLowConvolution
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDiagram`
- `DictatorshipTesting.Paper.S05_Int_PMConvolution`
-/


/-!
Definition file for `matchingHighConvolution`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- High-character convolution side of `I - P_M`.

This is the complementary sum of the matching-cube Fourier idempotents indexed
by characters of support size at least two. -/
def matchingHighConvolution {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin M.edgeCount) => 2 ≤ S.card)),
      cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
        cubeChar S (cubeZero M.edgeCount)

end DictatorshipTesting
