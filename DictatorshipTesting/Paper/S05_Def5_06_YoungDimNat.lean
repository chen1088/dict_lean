import DictatorshipTesting.Paper.S05_Def5_05_YoungHookLength

/-!
Definition file for `youngDimNat`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting


/-- Natural-number hook-length dimension formula. -/
def youngDimNat {n : ℕ} (lam : YoungDiagram n) : ℕ :=
  Nat.factorial n / (youngCells lam).prod (youngHookLength lam)

end DictatorshipTesting
