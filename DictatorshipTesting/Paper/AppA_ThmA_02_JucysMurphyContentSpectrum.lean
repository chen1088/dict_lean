import DictatorshipTesting.Paper.S05_Int_JucysMurphyContentAction

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem A.2 (`thm:app-jucys-murphy-content`)
Title in paper: Jucys--Murphy content spectrum.

Status: proven internally.  The coefficient-function Jucys--Murphy recurrence,
the matching tableau-operator recurrence, and the resulting finite induction
are proved in `S05_Int_JucysMurphyContentAction`.
-/


noncomputable section

namespace DictatorshipTesting

/-- Faithful operator-level statement of Theorem A.2: for each A.1 action, the
actual Jucys--Murphy coefficient elements act as the explicit diagonal content
operators. -/
def AppA_ThmA_02_JucysMurphyContentActionStatement : Prop :=
  ∀ {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam),
    Nonempty (JucysMurphyContentActionData action)

/-- Faithful A.2 content-action statement. -/
def AppA_ThmA_02_JucysMurphyContentSpectrumStatement : Prop :=
  AppA_ThmA_02_JucysMurphyContentActionStatement

/-- Theorem A.2: every concrete Young orthogonal action carries the faithful
Jucys--Murphy content action. -/
theorem AppA_ThmA_02_jucysMurphyContentSpectrum :
    AppA_ThmA_02_JucysMurphyContentSpectrumStatement := by
  intro n lam action
  exact jucysMurphyContentActionData_nonempty action

end DictatorshipTesting
