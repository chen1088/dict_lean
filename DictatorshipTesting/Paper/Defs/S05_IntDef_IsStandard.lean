import DictatorshipTesting.Paper.Defs.S05_IntDef_IsOneRow
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_13b_CertificateExceptionalPredicates`
- `DictatorshipTesting.Paper.Defs.S05_IntDef_IsYoungSubdiagram`
- `DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs`
-/


/-!
Definition file for `IsStandard`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The standard Young diagram `(n-1,1)`. -/
def IsStandard {n : ℕ} (lam : YoungDiagram n) : Prop :=
  2 ≤ n ∧ youngRow lam 0 = n - 1 ∧ youngRow lam 1 = 1

end DictatorshipTesting
