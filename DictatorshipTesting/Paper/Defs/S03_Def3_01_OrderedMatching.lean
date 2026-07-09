import DictatorshipTesting.Paper.Defs.S02_Def2_24_IsCubeOneJunta

/-!
Definition file for `OrderedMatching`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
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
