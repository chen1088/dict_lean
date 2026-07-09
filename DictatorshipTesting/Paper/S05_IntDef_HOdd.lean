import DictatorshipTesting.Paper.S05_IntDef_HEven

/-!
Definition file for `hOdd`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Number of weight-at-least-two entries in the odd matching-branching multiset. -/
def hOdd (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  (oneBoxChildrenOdd m lam).sum (fun mu => hEven m mu)

end DictatorshipTesting
