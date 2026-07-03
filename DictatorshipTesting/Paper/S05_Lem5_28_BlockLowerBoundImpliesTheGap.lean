import DictatorshipTesting.Paper.Aux_SpectralBridgeFromCertificates_Legacy

/-!
Paper statement: Lemma 5.28 (`lem:block-lower-bound-gap`)
Title in paper: Block lower bound implies the gap.

Status: paper-facing wrapper around the existing algebraic spectral-gap
comparison.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Lemma 5.28: scalar lower bounds on all non-`U_1` blocks imply the matching
spectral gap. -/
theorem S05_Lem5_28_block_lower_bound_implies_gap {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (hscalar_lb : ∀ lam ∈ nonU1YoungBlocks n, c ≤ theta lam) :
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F := by
  exact SpectralGapFromBlockScalarLowerBounds c F blockEnergy theta
    hdecomp hu1 hscalarity hscalar_lb

end DictatorshipTesting
