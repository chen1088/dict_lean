/-!
Paper statement: Theorem A.1 (`thm:app-young-orthogonal`)
Title in paper: Young orthogonal realization.

Status: external: ingredient bundled into Theorem A.3.  This file is kept
separate from the internal Section 5 coordinate Coxeter proof: the classical
Young orthogonal/Specht realization is consumed in Lean through the packaged
spectral-block model axioms in `AppA_ThmA_03_RegularYoungBlockDecomposition`.
-/

/-
Direct reverse imports (generated):
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_ThmA_03_RegularYoungBlockDecomposition`
-/

noncomputable section

namespace DictatorshipTesting

/-- Marker proposition for the not-yet-formalized Theorem A.1.  It stands for
the classical Young orthogonal/Specht realization used by the packaged
spectral-block model input in Theorem A.3. -/
inductive AppA_ThmA_01_YoungOrthogonalRealizationStatement : Prop

/-- External input Theorem A.1: Young orthogonal realization. -/
axiom AppA_ThmA_01_youngOrthogonalRealization :
    AppA_ThmA_01_YoungOrthogonalRealizationStatement

end DictatorshipTesting
