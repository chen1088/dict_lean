import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.AppA_DefA_01_YoungOrthogonalActionData
import DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem A.1 (`thm:app-young-orthogonal`)
Title in paper: Young orthogonal realization.

Status: proven internally.  The type-A Coxeter normal form identifies adjacent
words modulo the relations of Lemma 5.1 with permutations.  The explicit Young
adjacent operators therefore define the required symmetric-group action.
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

/-- The faithful A.1 action, constructed from the complete type-A Coxeter
presentation and the adjacent Young operators of Lemma 5.1. -/
theorem AppA_ThmA_01_youngOrthogonalRealization :
    AppA_ThmA_01_YoungOrthogonalRealizationStatement := by
  unfold AppA_ThmA_01_YoungOrthogonalRealizationStatement
  unfold AppA_ThmA_01_YoungOrthogonalActionStatement
  intro n lam
  exact youngOrthogonalActionData_nonempty lam

end DictatorshipTesting
