import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_16_YoungBasisScalarCommutant`
-/

/-!
Paper statement: Definition 5.23 (`def:young-basis-scalar-commutant-input`).
Title in paper: Young-basis scalar commutant input.

Status: definition/interface. This is the exact scalarity input consumed
downstream by the spectral bridge.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.23 interface: scalarity of the averaged matching rejection on Young
blocks.  Proving it from Young's basis/Schur's lemma remains
representation-layer work. -/
abbrev S05_Def5_23_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) -> Real)
    (blockEnergy theta : YoungDiagram n -> Real) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

end DictatorshipTesting
