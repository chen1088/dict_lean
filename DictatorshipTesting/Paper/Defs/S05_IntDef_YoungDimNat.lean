import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungHookLength
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDim`
-/


/-!
Definition file for `youngDimNat`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting


/-- Natural-number hook-length dimension formula. -/
def youngDimNat {n : ℕ} (lam : YoungDiagram n) : ℕ :=
  Nat.factorial n / (youngCells lam).prod (youngHookLength lam)

end DictatorshipTesting
