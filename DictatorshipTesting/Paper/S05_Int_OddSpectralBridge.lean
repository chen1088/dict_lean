import DictatorshipTesting.Paper.S05_Int_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.S05_Int_SpectralBridgeAlgebra
import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Thm4_06_MatchingGap`
-/


/-!
Internal odd bridge used in the proof of Theorem 4.6. The algebraic bridge is
proved from the concrete Section 5 spectral-block model and Lemma 5.26.
-/

noncomputable section

namespace DictatorshipTesting

/-- Odd finite Young-diagram inequalities imply the matching
spectral gap, assuming the stated spectral-block model. -/
theorem S05_oddSpectralBridge_odd_spectral_bridge
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam))
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  exact matchingSpectralGap_of_odd_young_certificate m hm c hmodel hc hcert

/-- Odd spectral bridge before the
extra nonnegativity argument is threaded through. -/
theorem S05_oddSpectralBridge_oddSpectralGapFromCertificates
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  exact OddSpectralGapFromCertificates m hm c hmodel hcert

/-- Tableau-count version: the `tableauDim` finite certificate feeds
any dimension-parameterized odd spectral-block model. -/
theorem S05_oddSpectralBridge_tableauDim_oddSpectralGapFromCertificates
    (m : Nat) (hm : 2 <= m)
    (hmodel :
      SpectralBlockModelInputWithDim
        (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)) :
    MatchingSpectralGapConstant (2 * m + 1) (1 / 6 : ℝ) := by
  exact
    SpectralGapFromBlockModelWithDim
      (1 / 6 : ℝ)
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)
      hmodel
      (fun lam hrow hstd =>
        S05_Lem5_26_tableau_odd_certificate m hm lam hrow hstd)

end DictatorshipTesting
