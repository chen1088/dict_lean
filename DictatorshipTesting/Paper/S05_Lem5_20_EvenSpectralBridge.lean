import DictatorshipTesting.Paper.S05_Int_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.S05_Int_SpectralBridgeAlgebra
import DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Thm4_08_MatchingGap`
-/


/-!
Paper statement: Lemma 5.20 (`lem:spectral-certificate-even`)
Title in paper: Even spectral bridge.

Status: proven. The algebraic bridge is proved from an explicit
spectral-block model hypothesis. Lemma 5.19 supplies that model input from the
Appendix A representation-theoretic ingredients for the paper application.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.20: even finite Young-diagram inequalities imply the matching
spectral gap, assuming the stated spectral-block model. -/
theorem S05_Lem5_20_even_spectral_bridge
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact matchingSpectralGap_of_even_young_certificate m hm c hmodel hc hcert

/-- Lemma 5.20 paper-numbered alias for the even spectral bridge before the
extra nonnegativity argument is threaded through. -/
theorem S05_Lem5_20_evenSpectralGapFromCertificates
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact EvenSpectralGapFromCertificates m hm c hmodel hcert

/-- Lemma 5.20, tableau-count version: the tableauDim finite certificate feeds
any dimension-parameterized even spectral-block model. -/
theorem S05_Lem5_20_tableauDim_evenSpectralGapFromCertificates
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
        S05_Lem5_25_tableau_even_certificate m hm lam hrow hstd)

end DictatorshipTesting
