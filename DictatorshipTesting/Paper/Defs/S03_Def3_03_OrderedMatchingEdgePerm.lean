import DictatorshipTesting.Paper.Defs.S03_Def3_02_OrderedMatchingEdgeSwap
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_04_OrderedMatchingTau`
-/


/-!
Definition file for `OrderedMatching.edgePerm`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The `r`th matching transposition if the cube bit is on, otherwise identity. -/
def OrderedMatching.edgePerm {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) (r : Fin M.edgeCount) :
    Perm α :=
  if x r then M.edgeSwap r else 1

end DictatorshipTesting
