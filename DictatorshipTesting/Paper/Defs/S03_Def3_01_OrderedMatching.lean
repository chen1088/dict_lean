import DictatorshipTesting.Paper.Defs.S02_Def2_24_IsCubeOneJunta
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_02_OrderedMatchingEdgeSwap`
-/


/-!
Definition file for `OrderedMatching`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- An ordered matching, with edges recorded as ordered pairs for computation. -/
structure OrderedMatching (α : Type*) [DecidableEq α] where
  edgeCount : ℕ
  left : Fin edgeCount → α
  right : Fin edgeCount → α
  left_ne_right : ∀ r, left r ≠ right r
  edges_disjoint :
    ∀ {r s : Fin edgeCount}, r ≠ s →
      left r ≠ left s ∧ left r ≠ right s ∧
        right r ≠ left s ∧ right r ≠ right s

end DictatorshipTesting
