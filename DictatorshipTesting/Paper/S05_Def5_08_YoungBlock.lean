import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-!
Paper statement: Definition 5.8 (`def:young-block`)
Title in paper: Young block.

Status: definition/interface. The current Lean scaffold represents Young-block indices by
`YoungDiagram n` and packages the analytic block decomposition through the
interfaces in `Aux_SpectralBridgeRepresentationInputs`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Current Lean shadow of a Young block index. -/
abbrev S05_YoungBlock (n : Nat) := YoungDiagram n

/-- Definition 5.8 interface: numerical Young-block energy model for a function.
This is an alias for the existing representation-layer input structure. -/
abbrev S05_Def5_08_YoungBlockEnergyModel {n : Nat}
    (F : Perm (Fin n) → ℝ) :=
  YoungBlockEnergyModel F

/-- Definition 5.8 interface: the scalar matching model supplied by the future
representation layer. -/
abbrev S05_Def5_08_MatchingAverageScalarModel {n : Nat}
    (height : YoungDiagram n → ℝ) (F : Perm (Fin n) → ℝ)
    (blockEnergy : YoungDiagram n → ℝ) :=
  MatchingAverageScalarModel height F blockEnergy

/-- Definition 5.8 interface: compact spectral block model used downstream.
This is not a proof of the Young-block decomposition; it records the precise
input expected from the representation layer. -/
abbrev S05_Def5_08_SpectralBlockModelInput {n : Nat}
    (height : YoungDiagram n → ℝ) : Prop :=
  SpectralBlockModelInput height

end DictatorshipTesting
