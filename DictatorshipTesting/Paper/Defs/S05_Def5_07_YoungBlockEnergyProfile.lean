import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Definition 5.7 (`def:young-block-energy-profile`).
Title in paper: Young block.

Status: definition/interface. This is the numerical nonnegativity interface
for Young-block energy profiles used by Lemma 5.19.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.6 interface: nonnegative block-energy decomposition. This
aliases the existing numerical input, rather than proving the representation
theorem. -/
abbrev S05_Def5_07_YoungBlockEnergyProfile {n : Nat}
    (blockEnergy : YoungDiagram n -> Real) : Prop :=
  YoungBlockDecompositionInput blockEnergy

end DictatorshipTesting
