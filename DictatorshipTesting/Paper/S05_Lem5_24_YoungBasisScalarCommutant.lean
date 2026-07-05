import DictatorshipTesting.Paper.S05_Lem5_23_CentralAveragedRejection
import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-!
Paper statement: Lemma 5.24 (`lem:young-basis-scalar-commutant`)
Title in paper: Young-basis scalar commutant.

Status: paper-facing owner file for the rewritten Section 5 statement.  This
is a tableau/Specht-module commutant statement and is not proved in the current
finite scaffold.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.25 interface: scalarity of the averaged matching rejection on
Young blocks.  This is the exact scalarity input consumed downstream; proving
it from Young's basis/Schur's lemma remains representation-layer work. -/
abbrev S05_Lem5_24_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) → ℝ)
    (blockEnergy theta : YoungDiagram n → ℝ) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

/-- Lemma 5.25 interface projection: if the scalar commutant input holds, then
the averaged rejection is the weighted sum of block energies. -/
theorem S05_Lem5_24_matchingAverageScalarity_eq_sum {n : Nat}
    {F : Perm (Fin n) → ℝ}
    {blockEnergy theta : YoungDiagram n → ℝ}
    (h : S05_Lem5_24_YoungBasisScalarCommutantInput F blockEnergy theta) :
    matchingMeanProjectionError F =
      (nonU1YoungBlocks n).sum (fun lam => theta lam * blockEnergy lam) := by
  exact h

end DictatorshipTesting
