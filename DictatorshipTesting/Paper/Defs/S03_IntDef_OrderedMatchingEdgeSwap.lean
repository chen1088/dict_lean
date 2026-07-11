import DictatorshipTesting.Paper.Defs.S03_IntDef_OrderedMatching
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_OrderedMatchingEdgePerm`
-/


/-!
Definition file for `OrderedMatching.edgeSwap`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The transposition associated to one edge of an ordered matching. -/
def OrderedMatching.edgeSwap {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (r : Fin M.edgeCount) : Perm α :=
  pswap (M.left r) (M.right r)

end DictatorshipTesting
