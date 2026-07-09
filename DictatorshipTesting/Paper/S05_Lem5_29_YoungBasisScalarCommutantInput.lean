import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_29_YoungBasisScalarCommutant`
-/

/-!
Paper statement: Lemma 5.29 (`lem:young-basis-scalar-commutant`), scalarity
input component.
Title in paper: Young-basis scalar commutant.

Status: definition/interface. This is the exact scalarity input consumed
downstream by the spectral bridge.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.29 interface: scalarity of the averaged matching rejection on Young
blocks.  Proving it from Young's basis/Schur's lemma remains
representation-layer work. -/
abbrev S05_Lem5_29_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) -> Real)
    (blockEnergy theta : YoungDiagram n -> Real) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

end DictatorshipTesting
