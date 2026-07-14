import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- none
-/
/-!

Status: definition/interface. This is the numerical interface saying that the
one-row and standard Young blocks account exactly for the degree-one space.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.6 interface: `U_1` is represented by the one-row and standard
Young blocks in the numerical model. -/
abbrev S05_IntDef_U1CompatibleYoungBlockProfile {n : Nat}
    (F : Perm (Fin n) -> Real) (blockEnergy : YoungDiagram n -> Real) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

end DictatorshipTesting
