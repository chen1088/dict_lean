import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_08_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
/-!

Status: definition/interface. This is the numerical nonnegativity interface
for Young-block energy profiles used by Lemma 5.8.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.6 interface: nonnegative block-energy decomposition. This
aliases the existing numerical input, rather than proving the representation
theorem. -/
abbrev S05_IntDef_YoungBlockEnergyProfile {n : Nat}
    (blockEnergy : YoungDiagram n -> Real) : Prop :=
  YoungBlockDecompositionInput blockEnergy

end DictatorshipTesting
