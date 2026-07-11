import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_16_YoungBasisScalarCommutant`
-/

/-!
Paper statement: Definition 5.23 (`def:young-basis-scalar-commutant-input`).
Title in paper: Young-basis scalar commutant input.

Status: definition/interface. This names the exact scalarity predicate used by
the spectral bridge; Lemma 5.19 proves it for the concrete Young components.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.23 interface: scalarity of the averaged matching rejection on
Young blocks. -/
abbrev S05_Def5_23_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) -> Real)
    (blockEnergy theta : YoungDiagram n -> Real) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

end DictatorshipTesting
