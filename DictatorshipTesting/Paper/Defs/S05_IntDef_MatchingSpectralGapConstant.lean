import DictatorshipTesting.Paper.Defs.S05_IntDef_HOdd
import DictatorshipTesting.Paper.Defs.S02_IntDef_L2DistSqToU1
import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingMeanProjectionError
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Thm4_04_MatchingGap`
- `DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs`
-/


/-!
Definition file for `MatchingSpectralGapConstant`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The spectral gap assertion with constant `c`. -/
def MatchingSpectralGapConstant (n : ℕ) (c : ℝ) : Prop :=
  ∀ F : Perm (Fin n) → ℝ,
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F

end DictatorshipTesting
