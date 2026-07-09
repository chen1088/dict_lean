import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_38_YoungBasisScalarCommutant`
-/

/-!
Paper statement: Definition 5.37 (`def:young-basis-scalar-commutant-input`).
Title in paper: Young-basis scalar commutant input.

Status: definition/interface. This is the exact scalarity input consumed
downstream by the spectral bridge.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.37 interface: scalarity of the averaged matching rejection on Young
blocks.  Proving it from Young's basis/Schur's lemma remains
representation-layer work. -/
abbrev S05_Def5_37_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) -> Real)
    (blockEnergy theta : YoungDiagram n -> Real) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

end DictatorshipTesting
