import DictatorshipTesting.Paper.S05_Int_SpectralBridgeFromCertificates
import DictatorshipTesting.Paper.S05_Int_SpectralBridgeAlgebra
import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Thm4_06_MatchingGap`
-/


/-!
Internal even bridge used in the proof of Theorem 4.6. The algebraic bridge is
proved from the concrete Section 5 spectral-block model and Lemma 5.25.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even finite Young-diagram inequalities imply the matching
spectral gap, assuming the stated spectral-block model. -/
theorem S05_evenSpectralBridge_even_spectral_bridge
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact matchingSpectralGap_of_even_young_certificate m hm c hmodel hc hcert

/-- Even spectral bridge before the
extra nonnegativity argument is threaded through. -/
theorem S05_evenSpectralBridge_evenSpectralGapFromCertificates
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact EvenSpectralGapFromCertificates m hm c hmodel hcert

/-- Tableau-count version: the `tableauDim` finite certificate feeds
any dimension-parameterized even spectral-block model. -/
theorem S05_evenSpectralBridge_tableauDim_evenSpectralGapFromCertificates
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
