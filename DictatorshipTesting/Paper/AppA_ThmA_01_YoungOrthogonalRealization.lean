import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.AppA_DefA_01_YoungOrthogonalActionData

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem A.1 (`thm:app-young-orthogonal`)
Title in paper: Young orthogonal realization.

Status: external: ingredient bundled into Lemma 5.19.  This file is kept
separate from the internal Section 5 coordinate Coxeter proof: the classical
Young orthogonal/Specht realization is consumed in Lean through the Lemma 5.19
spectral-block assembly theorem in
`S05_Lem5_19_RegularYoungBlockDecomposition`.
-/


noncomputable section

namespace DictatorshipTesting

/-- Faithful operator-level statement of Theorem A.1: every tableau shape has
a Young orthogonal symmetric-group action realizing the explicit adjacent
operators. -/
def AppA_ThmA_01_YoungOrthogonalActionStatement : Prop :=
  ∀ {n : Nat} (lam : YoungDiagram (n + 1)),
    Nonempty (YoungOrthogonalActionData lam)

/-- A container for nonnegative block energies used by the trace/scalar
payload and the active spectral model.  Lemma 5.19 constructs this container
from its concrete orthogonal block decomposition. -/
structure AppA_YoungBlockEnergyData {n : Nat}
    (F : Perm (Fin n) -> ℝ) where
  blockEnergy : YoungDiagram n -> ℝ
  nonneg : YoungBlockDecompositionInput blockEnergy

/-- The theorem statement used by the active global spectral assembly is the
faithful operator-level Young orthogonal realization. -/
def AppA_ThmA_01_YoungOrthogonalRealizationStatement : Prop :=
  AppA_ThmA_01_YoungOrthogonalActionStatement

/-- External A.1 input in its faithful operator-level form. -/
axiom AppA_ThmA_01_youngOrthogonalRealization :
    AppA_ThmA_01_YoungOrthogonalRealizationStatement

end DictatorshipTesting
