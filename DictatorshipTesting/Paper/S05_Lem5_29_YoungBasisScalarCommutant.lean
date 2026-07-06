import DictatorshipTesting.Paper.S05_Lem5_28_CentralAveragedRejection
import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-!
Paper statement: Lemma 5.29 (`lem:young-basis-scalar-commutant`)
Title in paper: Young-basis scalar commutant.

Status: external: scalar commutant input.  This file exposes the scalarity input
consumed by the active spectral bridge.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.30 interface: scalarity of the averaged matching rejection on
Young blocks.  This is the exact scalarity input consumed downstream; proving
it from Young's basis/Schur's lemma remains representation-layer work. -/
abbrev S05_Lem5_29_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) → ℝ)
    (blockEnergy theta : YoungDiagram n → ℝ) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

/-- Lemma 5.30 interface projection: if the scalar commutant input holds, then
the averaged rejection is the weighted sum of block energies. -/
theorem S05_Lem5_29_matchingAverageScalarity_eq_sum {n : Nat}
    {F : Perm (Fin n) → ℝ}
    {blockEnergy theta : YoungDiagram n → ℝ}
    (h : S05_Lem5_29_YoungBasisScalarCommutantInput F blockEnergy theta) :
    matchingMeanProjectionError F =
      (nonU1YoungBlocks n).sum (fun lam => theta lam * blockEnergy lam) := by
  exact h

end DictatorshipTesting
