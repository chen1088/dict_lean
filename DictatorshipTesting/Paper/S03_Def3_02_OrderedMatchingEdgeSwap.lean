import DictatorshipTesting.Paper.S03_Def3_01_OrderedMatching

/-!
Definition file for `OrderedMatching.edgeSwap`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The transposition associated to one edge of an ordered matching. -/
def OrderedMatching.edgeSwap {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (r : Fin M.edgeCount) : Perm α :=
  pswap (M.left r) (M.right r)

end DictatorshipTesting
