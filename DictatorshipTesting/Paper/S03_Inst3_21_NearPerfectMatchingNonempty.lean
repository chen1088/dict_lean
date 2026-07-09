import DictatorshipTesting.Paper.S03_Inst3_20_NearPerfectMatchingFintype

/-!
Definition file for `nearPerfectMatchingNonempty`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

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
