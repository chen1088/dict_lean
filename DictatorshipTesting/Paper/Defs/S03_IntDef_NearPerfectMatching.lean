import DictatorshipTesting.Paper.Defs.S04_Def4_02b_MatchingLocalProjectionError
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_NearPerfectMatchingToOrdered`
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

noncomputable instance nearPerfectMatchingFintype (n : ℕ) :
    Fintype (NearPerfectMatching n) := by
  classical
  exact Fintype.ofInjective
    (fun M : NearPerfectMatching n => (M.left, M.right))
    (by
      intro M N h
      cases M
      cases N
      simp at h
      simp [h])

instance nearPerfectMatchingNonempty (n : ℕ) : Nonempty (NearPerfectMatching n) := by
  let left : Fin (n / 2) → Fin n :=
    fun r => ⟨2 * (r : ℕ), by
      have hr : (r : ℕ) < n / 2 := r.isLt
      omega⟩
  let right : Fin (n / 2) → Fin n :=
    fun r => ⟨2 * (r : ℕ) + 1, by
      have hr : (r : ℕ) < n / 2 := r.isLt
      omega⟩
  refine ⟨{ left := left, right := right, left_ne_right := ?_, edges_disjoint := ?_ }⟩
  · intro r h
    have hnat := congrArg Fin.val h
    dsimp [left, right] at hnat
    omega
  · intro r s hrs
    constructor
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [left] at hnat
      exact hrs (Fin.ext (by omega))
    constructor
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [left, right] at hnat
      omega
    constructor
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [left, right] at hnat
      omega
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [right] at hnat
      exact hrs (Fin.ext (by omega))

end DictatorshipTesting
