import DictatorshipTesting.Paper.Defs.S05_IntDef_IsYoungSubdiagram
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_IsVerticalTwoStripChild`
-/


/-!
Definition file for `IsHorizontalTwoStripChild`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- `lam / mu` is a horizontal two-strip. -/
def IsHorizontalTwoStripChild {n k : ℕ} (lam : YoungDiagram n)
    (mu : YoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam ((i : ℕ) + 1) ≤ youngRow mu i

end DictatorshipTesting
