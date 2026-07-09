import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Def5_08_YoungBlock`
- `DictatorshipTesting.Paper.S05_Lem5_32_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Definition 5.8 (`def:young-block`), `U_1`-identification
component.
Title in paper: Young block.

Status: definition/interface. This is the numerical interface saying that the
one-row and standard Young blocks account exactly for the degree-one space.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.8 interface: `U_1` is represented by the one-row and standard
Young blocks in the numerical model. -/
abbrev S05_Def5_08_U1YoungBlockIdentificationInput {n : Nat}
    (F : Perm (Fin n) -> Real) (blockEnergy : YoungDiagram n -> Real) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

end DictatorshipTesting
