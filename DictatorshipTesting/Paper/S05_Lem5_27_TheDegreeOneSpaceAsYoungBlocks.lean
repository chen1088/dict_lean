import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-!
Paper statement: Lemma 5.27 (`lem:U1-young-blocks`)
Title in paper: The degree-one space as Young blocks.

Status: the current Lean scaffold records this identification as the interface
`U1YoungBlockIdentificationInput` inside the spectral-block model.
-/

noncomputable section

namespace DictatorshipTesting

/-- Current Lean interface for the `U_1` Young-block identification. -/
abbrev S05_U1YoungBlockIdentification {n : Nat}
    (F : Perm (Fin n) -> ℝ) (blockEnergy : YoungDiagram n -> ℝ) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

end DictatorshipTesting
