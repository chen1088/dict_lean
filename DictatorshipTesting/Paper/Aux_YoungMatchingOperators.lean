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

/-- Young's adjacent operator for the `r`th edge of the canonical matching in
the even case.  The shape is written as `(2*m - 1) + 1` so it matches the
`n+1` convention of `youngAdjacentOperator` definitionally. -/
noncomputable def canonicalMatchingYoungOperatorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) : TableauSpace lam -> TableauSpace lam :=
  youngAdjacentOperator (canonicalMatchingAdjacentIndex m r)

/-- Young's adjacent operator for the `r`th edge of the canonical matching in
the odd case, leaving the final label unmatched. -/
noncomputable def canonicalMatchingYoungOperatorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) : TableauSpace lam -> TableauSpace lam :=
  youngAdjacentOperator (canonicalNearMatchingAdjacentIndex m r)

theorem canonicalMatchingYoungOperatorEven_involutive
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven r f) = f := by
  exact youngAdjacentOperator_sq (canonicalMatchingAdjacentIndex m r) f

theorem canonicalMatchingYoungOperatorOdd_involutive
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd r f) = f := by
  exact youngAdjacentOperator_sq (canonicalNearMatchingAdjacentIndex m r) f

theorem canonicalMatchingYoungOperatorEven_comm
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven s f) =
      canonicalMatchingYoungOperatorEven s
        (canonicalMatchingYoungOperatorEven r f) := by
  exact youngAdjacentOperator_comm_of_disjoint_indices
    (canonicalMatchingAdjacentIndex m r)
    (canonicalMatchingAdjacentIndex m s)
    (canonicalMatchingAdjacentIndex_disjoint m hrs) f

theorem canonicalMatchingYoungOperatorOdd_comm
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd s f) =
      canonicalMatchingYoungOperatorOdd s
        (canonicalMatchingYoungOperatorOdd r f) := by
  exact youngAdjacentOperator_comm_of_disjoint_indices
    (canonicalNearMatchingAdjacentIndex m r)
    (canonicalNearMatchingAdjacentIndex m s)
    (canonicalNearMatchingAdjacentIndex_disjoint m hrs) f

end DictatorshipTesting
