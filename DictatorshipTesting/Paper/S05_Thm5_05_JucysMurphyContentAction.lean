import DictatorshipTesting.Paper.S05_Int_JucysMurphyContentAction

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem 5.5 (`thm:jucys-murphy-content`)
Title in paper: Jucys--Murphy content action.

Status: proven internally.  The coefficient-function Jucys--Murphy recurrence,
the matching tableau-operator recurrence, and the resulting finite induction
are proved in `S05_Int_JucysMurphyContentAction`.
-/


noncomputable section

namespace DictatorshipTesting

/-- Faithful operator-level statement of Theorem 5.5: for each Young action, the
actual Jucys--Murphy coefficient elements act as the explicit diagonal content
operators. -/
def S05_Thm5_05_JucysMurphyContentActionStatement : Prop :=
  ∀ {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam),
    Nonempty (JucysMurphyContentActionData action)

/-- Theorem 5.5: every concrete Young orthogonal action carries the faithful
Jucys--Murphy content action. -/
theorem S05_Thm5_05_jucysMurphyContentAction :
    S05_Thm5_05_JucysMurphyContentActionStatement := by
  intro n lam action
  exact jucysMurphyContentActionData_nonempty action

end DictatorshipTesting
