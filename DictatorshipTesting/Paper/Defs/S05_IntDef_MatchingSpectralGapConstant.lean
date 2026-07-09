import DictatorshipTesting.Paper.Defs.S05_IntDef_HOdd
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Thm4_10_MatchingGap`
- `DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs`
-/


/-!
Definition file for `MatchingSpectralGapConstant`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The spectral gap assertion with constant `c`. -/
def MatchingSpectralGapConstant (n : ℕ) (c : ℝ) : Prop :=
  ∀ F : Perm (Fin n) → ℝ,
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F

end DictatorshipTesting
