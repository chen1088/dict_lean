import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.Aux_SpectralBridgeDimensionParam
import DictatorshipTesting.Paper.S05_Lem5_41_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_49_OddCertificate

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Thm4_10_MatchingGap`
-/


/-!
Paper statement: Lemma 5.43 (`lem:spectral-certificate-odd`)
Title in paper: Odd spectral bridge.

Status: proven. The algebraic bridge is proved from an explicit
spectral-block model hypothesis. Lemma 5.41 supplies that model input from the
Appendix A representation-theoretic ingredients for the paper application.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.34: odd finite Young-diagram inequalities imply the matching
spectral gap, assuming the stated spectral-block model. -/
theorem S05_Lem5_43_odd_spectral_bridge
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam))
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  exact matchingSpectralGap_of_odd_young_certificate m hm c hmodel hc hcert

/-- Lemma 5.34 paper-numbered alias for the odd spectral bridge before the
extra nonnegativity argument is threaded through. -/
theorem S05_Lem5_43_oddSpectralGapFromCertificates
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m + 1) => hOdd m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m + 1),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hOdd m lam) :
    MatchingSpectralGapConstant (2 * m + 1) c := by
  exact OddSpectralGapFromCertificates m hm c hmodel hcert

/-- Lemma 5.34, tableau-count version: the tableauDim finite certificate feeds
any dimension-parameterized odd spectral-block model. -/
theorem S05_Lem5_43_tableauDim_oddSpectralGapFromCertificates
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
        S05_Lem5_49_tableau_odd_certificate m hm lam hrow hstd)

end DictatorshipTesting
