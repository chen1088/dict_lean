import DictatorshipTesting.Paper.Aux_CubeLowDegreeError
import DictatorshipTesting.Paper.Aux_OrderedMatchingTauMul

/-!
# Legacy helper: local projection as convolution

This was a numbered lemma in an older Section 5 draft.  The current latest
paper draft no longer has a separate `PM`-convolution lemma, so this file is
kept as an auxiliary helper rather than a paper-facing statement file.
-/

namespace DictatorshipTesting

/-- Legacy local-projection convolution identity. -/
theorem L5_1_PMConvolution {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) :
    matchingLocalProjection M F = matchingLowConvolution M F ∧
      (fun π => F π - matchingLocalProjection M F π) =
        matchingHighConvolution M F := by
  constructor
  · funext π
    rfl
  · funext π
    let g : Cube M.edgeCount → ℝ := fun x => F (π * M.tau x)
    have hzero : g (cubeZero M.edgeCount) = F π := by
      dsimp [g]
      rw [orderedMatching_tau_zero]
      simp
    have hres :
        g (cubeZero M.edgeCount) -
            cubeLowDegreeOnePart g (cubeZero M.edgeCount) =
          ∑ S : Finset (Fin M.edgeCount),
            cubeFourierCoeff
                (fun x : Cube M.edgeCount => g x - cubeLowDegreeOnePart g x) S *
              cubeChar S (cubeZero M.edgeCount) := by
      exact L2_3_cubeFourier_expansion M.edgeCount
        (fun x : Cube M.edgeCount => g x - cubeLowDegreeOnePart g x)
        (cubeZero M.edgeCount)
    unfold matchingHighConvolution
    calc
      F π - matchingLocalProjection M F π =
          g (cubeZero M.edgeCount) -
            cubeLowDegreeOnePart g (cubeZero M.edgeCount) := by
            simp [g, matchingLocalProjection, hzero]
      _ =
          ∑ S : Finset (Fin M.edgeCount),
            cubeFourierCoeff
                (fun x : Cube M.edgeCount => g x - cubeLowDegreeOnePart g x) S *
              cubeChar S (cubeZero M.edgeCount) := hres
      _ =
          ∑ S ∈
              Finset.univ.filter
                (fun S : Finset (Fin M.edgeCount) => 2 ≤ S.card),
            cubeFourierCoeff g S * cubeChar S (cubeZero M.edgeCount) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro S _hS
            by_cases hhigh : 2 ≤ S.card
            · simp [cubeFourierCoeff_lowDegreeResidual, hhigh]
            · simp [cubeFourierCoeff_lowDegreeResidual, hhigh]

end DictatorshipTesting
