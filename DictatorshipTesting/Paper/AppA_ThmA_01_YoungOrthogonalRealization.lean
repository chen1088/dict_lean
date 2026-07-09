import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_LemA_03_DegreeOneYoungBlockIdentification`
- `DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum`
- `DictatorshipTesting.Paper.S05_Lem5_18_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem A.1 (`thm:app-young-orthogonal`)
Title in paper: Young orthogonal realization.

Status: external: ingredient bundled into Lemma 5.18.  This file is kept
separate from the internal Section 5 coordinate Coxeter proof: the classical
Young orthogonal/Specht realization is consumed in Lean through the Lemma 5.18
spectral-block assembly theorem in
`S05_Lem5_18_RegularYoungBlockDecomposition`.
-/


noncomputable section

namespace DictatorshipTesting

/-- The block-energy data supplied by the Young orthogonal realization.  This
is the Lean-facing numerical shadow of decomposing a function into Young
blocks: each block receives a nonnegative squared energy. -/
structure AppA_YoungBlockEnergyData {n : Nat}
    (F : Perm (Fin n) -> ℝ) where
  blockEnergy : YoungDiagram n -> ℝ
  nonneg : YoungBlockDecompositionInput blockEnergy

/-- Theorem A.1 interface: every function has Young-block energy data. -/
def AppA_ThmA_01_YoungOrthogonalRealizationStatement : Prop :=
  ∀ {n : Nat} (F : Perm (Fin n) -> ℝ),
    Nonempty (AppA_YoungBlockEnergyData F)

/-- External input Theorem A.1: Young orthogonal realization. -/
axiom AppA_ThmA_01_youngOrthogonalRealization :
    AppA_ThmA_01_YoungOrthogonalRealizationStatement

end DictatorshipTesting
