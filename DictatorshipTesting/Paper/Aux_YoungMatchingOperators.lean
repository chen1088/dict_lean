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

/-- The `+` projection vector associated to an even matching edge is a
`+1` eigenvector. -/
theorem canonicalMatchingYoungOperatorEven_plusEigenVec
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T + canonicalMatchingYoungOperatorEven r f T) =
      fun T => f T + canonicalMatchingYoungOperatorEven r f T := by
  unfold canonicalMatchingYoungOperatorEven
  rw [youngAdjacentOperator_add,
    youngAdjacentOperator_sq (canonicalMatchingAdjacentIndex m r) f]
  funext T
  ring

/-- The `-` projection vector associated to an even matching edge is a
`-1` eigenvector. -/
theorem canonicalMatchingYoungOperatorEven_minusEigenVec
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T - canonicalMatchingYoungOperatorEven r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorEven r f T) := by
  unfold canonicalMatchingYoungOperatorEven
  rw [show
      (fun T =>
          f T - youngAdjacentOperator (canonicalMatchingAdjacentIndex m r) f T) =
        (fun T =>
          f T + (fun U =>
            - youngAdjacentOperator (canonicalMatchingAdjacentIndex m r) f U) T) by
        rfl]
  rw [youngAdjacentOperator_add, youngAdjacentOperator_neg,
    youngAdjacentOperator_sq (canonicalMatchingAdjacentIndex m r) f]
  funext T
  ring

/-- The `+` projection vector associated to an odd matching edge is a
`+1` eigenvector. -/
theorem canonicalMatchingYoungOperatorOdd_plusEigenVec
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T + canonicalMatchingYoungOperatorOdd r f T) =
      fun T => f T + canonicalMatchingYoungOperatorOdd r f T := by
  unfold canonicalMatchingYoungOperatorOdd
  rw [youngAdjacentOperator_add,
    youngAdjacentOperator_sq (canonicalNearMatchingAdjacentIndex m r) f]
  funext T
  ring

/-- The `-` projection vector associated to an odd matching edge is a
`-1` eigenvector. -/
theorem canonicalMatchingYoungOperatorOdd_minusEigenVec
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T - canonicalMatchingYoungOperatorOdd r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorOdd r f T) := by
  unfold canonicalMatchingYoungOperatorOdd
  rw [show
      (fun T =>
          f T - youngAdjacentOperator (canonicalNearMatchingAdjacentIndex m r) f T) =
        (fun T =>
          f T + (fun U =>
            - youngAdjacentOperator (canonicalNearMatchingAdjacentIndex m r) f U) T) by
        rfl]
  rw [youngAdjacentOperator_add, youngAdjacentOperator_neg,
    youngAdjacentOperator_sq (canonicalNearMatchingAdjacentIndex m r) f]
  funext T
  ring

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

/-- Compose a list of endomorphisms in the displayed order. -/
def composeOperatorList {V : Type*} : List (V -> V) -> V -> V
  | [] => id
  | op :: ops => fun v => op (composeOperatorList ops v)

@[simp] theorem composeOperatorList_replicate_id {V : Type*} (m : Nat) :
    composeOperatorList (List.replicate m (id : V -> V)) = id := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext v
      simp [List.replicate, composeOperatorList, ih]

/-- The edge operator selected by one cube bit in the even case. -/
noncomputable def canonicalMatchingYoungOperatorEvenBit
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : Cube m) (r : Fin m) : TableauSpace lam -> TableauSpace lam :=
  if x r then canonicalMatchingYoungOperatorEven r else id

/-- The edge operator selected by one cube bit in the odd case. -/
noncomputable def canonicalMatchingYoungOperatorOddBit
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : Cube m) (r : Fin m) : TableauSpace lam -> TableauSpace lam :=
  if x r then canonicalMatchingYoungOperatorOdd r else id

/-- Fixed-order product action of the canonical matching cube in the even case. -/
noncomputable def canonicalMatchingCubeOperatorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : Cube m) : TableauSpace lam -> TableauSpace lam :=
  composeOperatorList
    (List.ofFn fun r : Fin m =>
      canonicalMatchingYoungOperatorEvenBit (lam := lam) x r)

/-- Fixed-order product action of the canonical matching cube in the odd case. -/
noncomputable def canonicalMatchingCubeOperatorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : Cube m) : TableauSpace lam -> TableauSpace lam :=
  composeOperatorList
    (List.ofFn fun r : Fin m =>
      canonicalMatchingYoungOperatorOddBit (lam := lam) x r)

theorem canonicalMatchingCubeOperatorEven_zero
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)} :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeZero m) = id := by
  rw [canonicalMatchingCubeOperatorEven]
  rw [show
      (List.ofFn fun r : Fin m =>
        canonicalMatchingYoungOperatorEvenBit (lam := lam) (cubeZero m) r) =
        List.ofFn (fun _ : Fin m => (id : TableauSpace lam -> TableauSpace lam)) by
        simp [canonicalMatchingYoungOperatorEvenBit, cubeZero]]
  rw [List.ofFn_const]
  exact composeOperatorList_replicate_id m

theorem canonicalMatchingCubeOperatorOdd_zero
    {m : Nat} {lam : YoungDiagram (2 * m + 1)} :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeZero m) = id := by
  rw [canonicalMatchingCubeOperatorOdd]
  rw [show
      (List.ofFn fun r : Fin m =>
        canonicalMatchingYoungOperatorOddBit (lam := lam) (cubeZero m) r) =
        List.ofFn (fun _ : Fin m => (id : TableauSpace lam -> TableauSpace lam)) by
        simp [canonicalMatchingYoungOperatorOddBit, cubeZero]]
  rw [List.ofFn_const]
  exact composeOperatorList_replicate_id m

theorem canonicalMatchingYoungOperatorEven_basis_sameRow
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact youngAdjacentOperator_basis_sameRow
    T (canonicalMatchingAdjacentIndex m r) hrow

theorem canonicalMatchingYoungOperatorEven_basis_sameCol
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact youngAdjacentOperator_basis_sameCol
    T (canonicalMatchingAdjacentIndex m r) hcol

theorem canonicalMatchingYoungOperatorEven_basis_sameRow_eigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  rw [canonicalMatchingYoungOperatorEven_basis_sameRow T r hrow]
  simp

theorem canonicalMatchingYoungOperatorEven_basis_sameCol_eigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  rw [canonicalMatchingYoungOperatorEven_basis_sameCol T r hcol]
  funext S
  simp

theorem canonicalMatchingYoungOperatorEven_basis_swappable_self_value
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact youngAdjacentOperator_basis_swappable_self_value
    T (canonicalMatchingAdjacentIndex m r) hrow_ne hcol_ne

theorem canonicalMatchingYoungOperatorEven_basis_swappable_swap_value
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T)
        (adjacentSwapTableau T (canonicalMatchingAdjacentIndex m r)
          hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact youngAdjacentOperator_basis_swappable_swap_value
    T (canonicalMatchingAdjacentIndex m r) hrow_ne hcol_ne

theorem canonicalMatchingYoungOperatorOdd_basis_sameRow
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact youngAdjacentOperator_basis_sameRow
    T (canonicalNearMatchingAdjacentIndex m r) hrow

theorem canonicalMatchingYoungOperatorOdd_basis_sameCol
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact youngAdjacentOperator_basis_sameCol
    T (canonicalNearMatchingAdjacentIndex m r) hcol

theorem canonicalMatchingYoungOperatorOdd_basis_sameRow_eigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  rw [canonicalMatchingYoungOperatorOdd_basis_sameRow T r hrow]
  simp

theorem canonicalMatchingYoungOperatorOdd_basis_sameCol_eigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  rw [canonicalMatchingYoungOperatorOdd_basis_sameCol T r hcol]
  funext S
  simp

theorem canonicalMatchingYoungOperatorOdd_basis_swappable_self_value
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact youngAdjacentOperator_basis_swappable_self_value
    T (canonicalNearMatchingAdjacentIndex m r) hrow_ne hcol_ne

theorem canonicalMatchingYoungOperatorOdd_basis_swappable_swap_value
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T)
        (adjacentSwapTableau T (canonicalNearMatchingAdjacentIndex m r)
          hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact youngAdjacentOperator_basis_swappable_swap_value
    T (canonicalNearMatchingAdjacentIndex m r) hrow_ne hcol_ne

end DictatorshipTesting
