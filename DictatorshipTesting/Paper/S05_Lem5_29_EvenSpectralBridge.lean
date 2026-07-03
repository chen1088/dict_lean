import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates_Legacy

/-!
Paper statement: Lemma 5.29 (`lem:spectral-certificate-even`)
Title in paper: Even spectral bridge.

Status: paper-facing wrapper around the existing even spectral bridge, still
conditional on the explicit spectral-block model input.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.29: even finite Young-diagram inequalities imply the matching
spectral gap, conditional on the spectral-block model. -/
theorem S05_Lem5_29_even_spectral_bridge
    (m : Nat) (hm : 2 ≤ m) (c : ℝ)
    (hmodel : SpectralBlockModelInput
      (fun lam : YoungDiagram (2 * m) => hEven m lam))
    (hc : 0 ≤ c)
    (hcert :
      ∀ lam : YoungDiagram (2 * m),
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * youngDim lam ≤ hEven m lam) :
    MatchingSpectralGapConstant (2 * m) c := by
  exact matchingSpectralGap_of_even_young_certificate m hm c hmodel hc hcert

end DictatorshipTesting
