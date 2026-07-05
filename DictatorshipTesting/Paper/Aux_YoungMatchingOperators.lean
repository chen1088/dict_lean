import DictatorshipTesting.Paper.Aux_YoungOrthogonal

/-!
# Canonical matching operators in Young coordinates

This helper packages the elementary operator algebra for the canonical matching
whose edges pair adjacent labels `(0,1), (2,3), ...`.  It deliberately stays at
the concrete tableau-coordinate level; it does not assert the Specht-module
restriction/eigenbasis theorem.
-/

noncomputable section

namespace DictatorshipTesting

/-- The adjacent-generator index for the `r`th edge of the canonical perfect
matching on `2*m` labels. -/
def canonicalMatchingAdjacentIndex (m : Nat) (r : Fin m) : Fin (2 * m - 1) :=
  ⟨2 * (r : Nat), by
    have hr : (r : Nat) < m := r.isLt
    omega⟩

/-- The adjacent-generator index for the `r`th edge of the canonical
near-perfect matching on `2*m+1` labels. -/
def canonicalNearMatchingAdjacentIndex (m : Nat) (r : Fin m) : Fin (2 * m) :=
  ⟨2 * (r : Nat), by
    have hr : (r : Nat) < m := r.isLt
    omega⟩

@[simp] theorem canonicalMatchingAdjacentIndex_val
    (m : Nat) (r : Fin m) :
    (canonicalMatchingAdjacentIndex m r : Nat) = 2 * (r : Nat) := by
  rfl

@[simp] theorem canonicalNearMatchingAdjacentIndex_val
    (m : Nat) (r : Fin m) :
    (canonicalNearMatchingAdjacentIndex m r : Nat) = 2 * (r : Nat) := by
  rfl

/-- Distinct canonical matching edges are disjoint adjacent transpositions in
the even/perfect case. -/
theorem canonicalMatchingAdjacentIndex_disjoint
    (m : Nat) {r s : Fin m} (hrs : r ≠ s) :
    adjacentIndexDisjoint
      (canonicalMatchingAdjacentIndex m r)
      (canonicalMatchingAdjacentIndex m s) := by
  have hrsNat : (r : Nat) ≠ (s : Nat) := by
    intro h
    exact hrs (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hrsNat with hlt | hgt
  · exact Or.inl (by
      simp [canonicalMatchingAdjacentIndex]
      omega)
  · exact Or.inr (by
      simp [canonicalMatchingAdjacentIndex]
      omega)

/-- Distinct canonical matching edges are disjoint adjacent transpositions in
the odd/near-perfect case. -/
theorem canonicalNearMatchingAdjacentIndex_disjoint
    (m : Nat) {r s : Fin m} (hrs : r ≠ s) :
    adjacentIndexDisjoint
      (canonicalNearMatchingAdjacentIndex m r)
      (canonicalNearMatchingAdjacentIndex m s) := by
  have hrsNat : (r : Nat) ≠ (s : Nat) := by
    intro h
    exact hrs (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hrsNat with hlt | hgt
  · exact Or.inl (by
      simp [canonicalNearMatchingAdjacentIndex]
      omega)
  · exact Or.inr (by
      simp [canonicalNearMatchingAdjacentIndex]
      omega)

end DictatorshipTesting
