import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.AppA_DefA_01_YoungOrthogonalActionData

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_LemA_03_DegreeOneYoungBlockIdentification`
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

/-- The block-energy data supplied by the Young orthogonal realization.  This
is the Lean-facing numerical shadow of decomposing a function into Young
blocks: each block receives a nonnegative squared energy. -/
structure AppA_YoungBlockEnergyData {n : Nat}
    (F : Perm (Fin n) -> ℝ) where
  blockEnergy : YoungDiagram n -> ℝ
  nonneg : YoungBlockDecompositionInput blockEnergy

/-- Old numerical A.1 shadow used by the active global spectral assembly.
This is not the faithful operator-level statement above. -/
def AppA_ThmA_01_YoungOrthogonalRealizationStatement : Prop :=
  ∀ {n : Nat} (F : Perm (Fin n) -> ℝ),
    Nonempty (AppA_YoungBlockEnergyData F)

/-- Existing external A.1 input.  Its numerical type is retained until the
regular Young-block decomposition can be constructed from the faithful action
statement without breaking the active Theorem 4.8 route. -/
axiom AppA_ThmA_01_youngOrthogonalRealization :
    AppA_ThmA_01_YoungOrthogonalRealizationStatement

end DictatorshipTesting
