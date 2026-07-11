import DictatorshipTesting.Paper.S03_IntInst_NearPerfectMatchingNonempty
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingMeanProjectionError`
-/


/-!
Definition file for `NearPerfectMatching.toOrdered`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- View a near-perfect matching as the generic ordered matching structure. -/
def NearPerfectMatching.toOrdered {n : ℕ}
    (M : NearPerfectMatching n) : OrderedMatching (Fin n) where
  edgeCount := n / 2
  left := M.left
  right := M.right
  left_ne_right := M.left_ne_right
  edges_disjoint := by
    intro r s hrs
    exact M.edges_disjoint hrs

end DictatorshipTesting
