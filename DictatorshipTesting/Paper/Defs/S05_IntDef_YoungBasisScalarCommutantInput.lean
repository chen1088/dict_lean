import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_08_YoungBasisScalarCommutant`
-/

/-!

Status: definition/interface. This names the exact scalarity predicate used by
the spectral bridge; Lemma 5.22 proves it for the concrete Young components.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.23 interface: scalarity of the averaged matching rejection on
Young blocks. -/
abbrev S05_IntDef_YoungBasisScalarCommutantInput {n : Nat}
    (F : Perm (Fin n) -> Real)
    (blockEnergy theta : YoungDiagram n -> Real) : Prop :=
  MatchingAverageScalarityInput F blockEnergy theta

end DictatorshipTesting
