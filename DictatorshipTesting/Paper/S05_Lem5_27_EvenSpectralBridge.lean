import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.Aux_SpectralBridgeDimensionParam
import DictatorshipTesting.Paper.S05_Lem5_32_EvenCertificate

/-!
Paper statement: Lemma 5.27 (`lem:spectral-certificate-even`)
Title in paper: Even spectral bridge.

Status: the algebraic bridge is proved from an explicit spectral-block model
hypothesis. Appendix A supplies that representation-theoretic model input for
the paper application.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.27: even finite Young-diagram inequalities imply the matching
spectral gap, assuming the stated spectral-block model. -/
theorem S05_Lem5_27_even_spectral_bridge
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact matchingSpectralGap_of_even_young_certificate m hm c hmodel hc hcert

/-- Lemma 5.27 paper-numbered alias for the even spectral bridge before the
extra nonnegativity argument is threaded through. -/
theorem S05_Lem5_27_evenSpectralGapFromCertificates
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact EvenSpectralGapFromCertificates m hm c hmodel hcert

/-- Lemma 5.27, tableau-count version: the tableauDim finite certificate feeds
any dimension-parameterized even spectral-block model. -/
theorem S05_Lem5_27_tableauDim_evenSpectralGapFromCertificates
    (m : Nat) (hm : 2 <= m)
    (hmodel :
      SpectralBlockModelInputWithDim
        (fun lam : YoungDiagram (2 * m) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)) :
    MatchingSpectralGapConstant (2 * m) (1 / 5 : ℝ) := by
  exact
    SpectralGapFromBlockModelWithDim
      (1 / 5 : ℝ)
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)
      hmodel
      (fun lam hrow hstd =>
        S05_Lem5_32_tableau_even_certificate m hm lam hrow hstd)

end DictatorshipTesting
