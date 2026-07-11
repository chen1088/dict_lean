import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungOrthogonalActionData
import DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Theorem 5.3 (`thm:young-orthogonal-action`)
Title in paper: Young orthogonal action.

Status: proven internally.  The type-A Coxeter normal form identifies adjacent
words modulo the relations of Lemma 5.1 with permutations.  The explicit Young
adjacent operators therefore define the required symmetric-group action.
-/


noncomputable section

namespace DictatorshipTesting

/-- Faithful operator-level statement of Theorem 5.3: every tableau shape has
a Young orthogonal symmetric-group action realizing the explicit adjacent
operators. -/
def S05_Thm5_03_YoungOrthogonalActionStatement : Prop :=
  ∀ {n : Nat} (lam : YoungDiagram (n + 1)),
    Nonempty (YoungOrthogonalActionData lam)

/-- The faithful Young action, constructed from the complete type-A Coxeter
presentation and the adjacent Young operators of Lemma 5.1. -/
theorem S05_Thm5_03_youngOrthogonalAction :
    S05_Thm5_03_YoungOrthogonalActionStatement := by
  unfold S05_Thm5_03_YoungOrthogonalActionStatement
  intro n lam
  exact youngOrthogonalActionData_nonempty lam

end DictatorshipTesting
