import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingHighConvolution
import DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError
import AlgebraicLibrary.Combinatorics.OrderedMatching.CubeHom

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents`
- `DictatorshipTesting.Paper.S05_Lem5_14_MatchingFourierProjections`
-/
/-!
# Internal local projection as convolution

This internal Section 5 module proves the local-projection convolution identity used by the
paper-facing local-truncation and averaged-rejection files.
-/

namespace DictatorshipTesting

/-- Local-projection convolution identity.  The theorem name is preserved for
compatibility with existing imports. -/
theorem S05_Int_PMConvolution {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) :
    matchingLocalProjection M F = matchingLowConvolution M F ∧
      (fun π => F π - matchingLocalProjection M F π) =
        matchingHighConvolution M F := by
  constructor
  · funext π
    rfl
  · funext π
    let g : FinCube M.edgeCount → ℝ := fun x => F (π * M.tau x)
    have hzero : g (finCubeZero M.edgeCount) = F π := by
      dsimp [g]
      rw [orderedMatching_tau_zero]
      simp
    have hres :
        g (finCubeZero M.edgeCount) -
            cubeLowDegreeOnePart g (finCubeZero M.edgeCount) =
          ∑ S : Finset (Fin M.edgeCount),
            cubeFourierCoeff
                (fun x : FinCube M.edgeCount => g x - cubeLowDegreeOnePart g x) S *
              cubeChar S (finCubeZero M.edgeCount) := by
      exact S02_Lem2_03_cubeFourier_expansion M.edgeCount
        (fun x : FinCube M.edgeCount => g x - cubeLowDegreeOnePart g x)
        (finCubeZero M.edgeCount)
    unfold matchingHighConvolution
    calc
      F π - matchingLocalProjection M F π =
          g (finCubeZero M.edgeCount) -
            cubeLowDegreeOnePart g (finCubeZero M.edgeCount) := by
            simp [g, matchingLocalProjection, hzero]
      _ =
          ∑ S : Finset (Fin M.edgeCount),
            cubeFourierCoeff
                (fun x : FinCube M.edgeCount => g x - cubeLowDegreeOnePart g x) S *
              cubeChar S (finCubeZero M.edgeCount) := hres
      _ =
          ∑ S ∈
              Finset.univ.filter
                (fun S : Finset (Fin M.edgeCount) => 2 ≤ S.card),
            cubeFourierCoeff g S * cubeChar S (finCubeZero M.edgeCount) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro S _hS
            by_cases hhigh : 2 ≤ S.card
            · simp [cubeFourierCoeff_lowDegreeResidual, hhigh]
            · simp [cubeFourierCoeff_lowDegreeResidual, hhigh]

end DictatorshipTesting
