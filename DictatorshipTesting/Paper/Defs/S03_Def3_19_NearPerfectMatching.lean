import DictatorshipTesting.Paper.Defs.S03_Def3_18_MatchingLocalProjectionError
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S03_Inst3_20_NearPerfectMatchingFintype`
-/


/-!
Definition file for `NearPerfectMatching`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- An ordered near-perfect matching on `Fin n`, with `n / 2` ordered edges.
For odd `n` this leaves one point unmatched; for even `n` it is perfect. -/
structure NearPerfectMatching (n : ℕ) where
  left : Fin (n / 2) → Fin n
  right : Fin (n / 2) → Fin n
  left_ne_right : ∀ r, left r ≠ right r
  edges_disjoint :
    ∀ {r s : Fin (n / 2)}, r ≠ s →
      left r ≠ left s ∧ left r ≠ right s ∧
        right r ≠ left s ∧ right r ≠ right s
deriving DecidableEq

end DictatorshipTesting
