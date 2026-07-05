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

theorem canonicalMatchingYoungOperatorEven_smul
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (c : ℝ) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r (c • f) =
      c • canonicalMatchingYoungOperatorEven r f := by
  unfold canonicalMatchingYoungOperatorEven
  funext T
  change
    youngAdjacentOperator (canonicalMatchingAdjacentIndex m r)
        (fun S => c * f S) T =
      c * youngAdjacentOperator (canonicalMatchingAdjacentIndex m r) f T
  exact congrFun
    (youngAdjacentOperator_smul (canonicalMatchingAdjacentIndex m r) c f) T

theorem canonicalMatchingYoungOperatorOdd_smul
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (c : ℝ) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r (c • f) =
      c • canonicalMatchingYoungOperatorOdd r f := by
  unfold canonicalMatchingYoungOperatorOdd
  funext T
  change
    youngAdjacentOperator (canonicalNearMatchingAdjacentIndex m r)
        (fun S => c * f S) T =
      c * youngAdjacentOperator (canonicalNearMatchingAdjacentIndex m r) f T
  exact congrFun
    (youngAdjacentOperator_smul (canonicalNearMatchingAdjacentIndex m r) c f) T

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

/-- Select either an involution `A i` or the identity from a Boolean bit. -/
def operatorBit {ι V : Type*} (A : ι -> V -> V) (x : ι -> Bool)
    (i : ι) : V -> V :=
  if x i then A i else id

/-- Fixed-order product of Boolean-selected operators along a list of indices. -/
def indexedOperatorListProduct {ι V : Type*} (A : ι -> V -> V)
    (x : ι -> Bool) : List ι -> V -> V
  | [] => id
  | i :: L => fun v => operatorBit A x i (indexedOperatorListProduct A x L v)

@[simp] theorem indexedOperatorListProduct_nil {ι V : Type*}
    (A : ι -> V -> V) (x : ι -> Bool) :
    indexedOperatorListProduct A x [] = id := by
  rfl

@[simp] theorem indexedOperatorListProduct_cons {ι V : Type*}
    (A : ι -> V -> V) (x : ι -> Bool) (i : ι) (L : List ι) :
    indexedOperatorListProduct A x (i :: L) =
      fun v => operatorBit A x i (indexedOperatorListProduct A x L v) := by
  rfl

theorem composeOperatorList_map_operatorBit {ι V : Type*}
    (A : ι -> V -> V) (x : ι -> Bool) (L : List ι) :
    composeOperatorList (L.map fun i => operatorBit A x i) =
      indexedOperatorListProduct A x L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      funext v
      simp [composeOperatorList, indexedOperatorListProduct, ih]

theorem operatorBit_comm {ι V : Type*} {A : ι -> V -> V}
    (hcomm : ∀ i j v, A i (A j v) = A j (A i v))
    (x y : ι -> Bool) (i j : ι) (v : V) :
    operatorBit A x i (operatorBit A y j v) =
      operatorBit A y j (operatorBit A x i v) := by
  unfold operatorBit
  by_cases hxi : x i <;> by_cases hyj : y j <;> simp [hxi, hyj, hcomm]

theorem operatorBit_xor_apply {ι V : Type*} {A : ι -> V -> V}
    (hinv : ∀ i v, A i (A i v) = v)
    (x y : ι -> Bool) (i : ι) (v : V) :
    operatorBit A (fun j => x j ^^ y j) i v =
      operatorBit A x i (operatorBit A y i v) := by
  unfold operatorBit
  by_cases hxi : x i <;> by_cases hyi : y i <;> simp [hxi, hyi, hinv]

theorem operatorBit_commute_indexedOperatorListProduct {ι V : Type*}
    {A : ι -> V -> V}
    (hcomm : ∀ i j v, A i (A j v) = A j (A i v))
    (x y : ι -> Bool) (i : ι) (L : List ι) (v : V) :
    operatorBit A y i (indexedOperatorListProduct A x L v) =
      indexedOperatorListProduct A x L (operatorBit A y i v) := by
  induction L generalizing v with
  | nil => rfl
  | cons j L ih =>
      simp [indexedOperatorListProduct]
      rw [operatorBit_comm (A := A) hcomm y x i j
        (indexedOperatorListProduct A x L v)]
      rw [ih]

theorem indexedOperatorListProduct_xor_apply {ι V : Type*}
    {A : ι -> V -> V}
    (hinv : ∀ i v, A i (A i v) = v)
    (hcomm : ∀ i j v, A i (A j v) = A j (A i v))
    (x y : ι -> Bool) (L : List ι) (v : V) :
    indexedOperatorListProduct A (fun i => x i ^^ y i) L v =
      indexedOperatorListProduct A x L (indexedOperatorListProduct A y L v) := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      simp [indexedOperatorListProduct]
      rw [ih]
      rw [operatorBit_xor_apply (A := A) hinv x y i
        (indexedOperatorListProduct A x L (indexedOperatorListProduct A y L v))]
      rw [operatorBit_commute_indexedOperatorListProduct
        (A := A) hcomm x y i L (indexedOperatorListProduct A y L v)]

/-- If each generator acts by a scalar on a vector, then the fixed-order
Boolean-selected product acts by the product of the selected scalars. -/
theorem indexedOperatorListProduct_eigen_apply {ι V : Type*} [MulAction ℝ V]
    {A : ι -> V -> V} {c : ι -> ℝ}
    (hA : ∀ i v, A i v = c i • v)
    (x : ι -> Bool) (L : List ι) (v : V) :
    indexedOperatorListProduct A x L v =
      ((L.map fun i => if x i then c i else 1).prod) • v := by
  induction L generalizing v with
  | nil =>
      simp [indexedOperatorListProduct]
  | cons i L ih =>
      by_cases hxi : x i
      · simp [indexedOperatorListProduct, operatorBit, hxi, hA, ih, mul_smul]
      · simp [indexedOperatorListProduct, operatorBit, hxi, ih]

/-- Fixed-vector version of `indexedOperatorListProduct_eigen_apply`: if one
vector is a simultaneous eigenvector and the operators are homogeneous on its
scalar multiples, then the product acts by the product of the eigenvalues. -/
theorem indexedOperatorListProduct_eigenvector_apply {ι V : Type*}
    [MulAction ℝ V]
    {A : ι -> V -> V} {c : ι -> ℝ} (v : V)
    (hsmul : ∀ i (a : ℝ), A i (a • v) = a • A i v)
    (hA : ∀ i, A i v = c i • v)
    (x : ι -> Bool) (L : List ι) :
    indexedOperatorListProduct A x L v =
      ((L.map fun i => if x i then c i else 1).prod) • v := by
  induction L with
  | nil =>
      simp [indexedOperatorListProduct]
  | cons i L ih =>
      by_cases hxi : x i
      · simp [indexedOperatorListProduct, operatorBit, hxi]
        rw [ih]
        rw [hsmul i ((L.map fun i => if x i then c i else 1).prod)]
        rw [hA i]
        rw [smul_smul]
        rw [mul_comm]
      · simp [indexedOperatorListProduct, operatorBit, hxi, ih]

/-- The sign of one matching-cube edge for a character support. -/
def matchingEdgeSign {m : Nat} (R : Finset (Fin m)) (r : Fin m) : ℝ :=
  if r ∈ R then -1 else 1

/-- The fixed-order product of selected edge signs is the matching-cube
character with the same support. -/
theorem matchingEdgeSign_finRange_product_eq_cubeChar
    {m : Nat} (R : Finset (Fin m)) (x : Cube m) :
    ((List.finRange m).map
      (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod =
      cubeChar R x := by
  change ((Finset.univ : Finset (Fin m)).val.map
      (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod =
      cubeChar R x
  change (Finset.univ : Finset (Fin m)).prod
      (fun r : Fin m => if x r then matchingEdgeSign R r else 1) =
      cubeChar R x
  unfold cubeChar matchingEdgeSign
  have hswap :
      (Finset.univ : Finset (Fin m)).prod
          (fun r : Fin m => if x r then (if r ∈ R then (-1 : ℝ) else 1) else 1) =
        (Finset.univ : Finset (Fin m)).prod
          (fun r : Fin m => if r ∈ R then (if x r then (-1 : ℝ) else 1) else 1) := by
    apply Finset.prod_congr rfl
    intro r _hr
    by_cases hx : x r <;> by_cases hr : r ∈ R <;> simp [hx, hr]
  rw [hswap]
  rw [Finset.prod_ite_mem_eq]

/-- Simultaneous eigenspace predicate for the canonical even matching edges. -/
def IsMatchingEigenvectorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  ∀ r : Fin m,
    canonicalMatchingYoungOperatorEven r f = matchingEdgeSign R r • f

/-- Simultaneous eigenspace predicate for the canonical odd matching edges. -/
def IsMatchingEigenvectorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  ∀ r : Fin m,
    canonicalMatchingYoungOperatorOdd r f = matchingEdgeSign R r • f

theorem IsMatchingEigenvectorEven.edge_mem
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorEven f R) {r : Fin m} (hr : r ∈ R) :
    canonicalMatchingYoungOperatorEven r f = (-1 : ℝ) • f := by
  simpa [IsMatchingEigenvectorEven, matchingEdgeSign, hr] using hf r

theorem IsMatchingEigenvectorEven.edge_notMem
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorEven f R) {r : Fin m} (hr : r ∉ R) :
    canonicalMatchingYoungOperatorEven r f = (1 : ℝ) • f := by
  simpa [IsMatchingEigenvectorEven, matchingEdgeSign, hr] using hf r

theorem IsMatchingEigenvectorOdd.edge_mem
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorOdd f R) {r : Fin m} (hr : r ∈ R) :
    canonicalMatchingYoungOperatorOdd r f = (-1 : ℝ) • f := by
  simpa [IsMatchingEigenvectorOdd, matchingEdgeSign, hr] using hf r

theorem IsMatchingEigenvectorOdd.edge_notMem
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorOdd f R) {r : Fin m} (hr : r ∉ R) :
    canonicalMatchingYoungOperatorOdd r f = (1 : ℝ) • f := by
  simpa [IsMatchingEigenvectorOdd, matchingEdgeSign, hr] using hf r

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

theorem canonicalMatchingCubeOperatorEven_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorEven (lam := lam) r)
        x (List.finRange m) := by
  rw [canonicalMatchingCubeOperatorEven, List.ofFn_eq_map]
  change
    composeOperatorList
        (List.map
          (fun r : Fin m =>
            operatorBit
              (fun r : Fin m => canonicalMatchingYoungOperatorEven (lam := lam) r)
              x r)
          (List.finRange m)) =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorEven (lam := lam) r)
        x (List.finRange m)
  rw [composeOperatorList_map_operatorBit]

theorem canonicalMatchingCubeOperatorOdd_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorOdd (lam := lam) r)
        x (List.finRange m) := by
  rw [canonicalMatchingCubeOperatorOdd, List.ofFn_eq_map]
  change
    composeOperatorList
        (List.map
          (fun r : Fin m =>
            operatorBit
              (fun r : Fin m => canonicalMatchingYoungOperatorOdd (lam := lam) r)
              x r)
          (List.finRange m)) =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorOdd (lam := lam) r)
        x (List.finRange m)
  rw [composeOperatorList_map_operatorBit]

theorem canonicalMatchingCubeOperatorEven_xor_apply
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x y : Cube m) (f : TableauSpace lam) :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeXor x y) f =
      canonicalMatchingCubeOperatorEven (lam := lam) x
        (canonicalMatchingCubeOperatorEven (lam := lam) y f) := by
  let A : Fin m -> TableauSpace lam -> TableauSpace lam :=
    fun r => canonicalMatchingYoungOperatorEven (lam := lam) r
  have hinv : ∀ r v, A r (A r v) = v := by
    intro r v
    exact canonicalMatchingYoungOperatorEven_involutive r v
  have hcomm : ∀ r s v, A r (A s v) = A s (A r v) := by
    intro r s v
    by_cases hrs : r = s
    · subst s
      rfl
    · exact canonicalMatchingYoungOperatorEven_comm hrs v
  rw [canonicalMatchingCubeOperatorEven_eq_indexedProduct (lam := lam)]
  rw [canonicalMatchingCubeOperatorEven_eq_indexedProduct (lam := lam) x]
  rw [canonicalMatchingCubeOperatorEven_eq_indexedProduct (lam := lam) y]
  exact indexedOperatorListProduct_xor_apply
    (A := A) hinv hcomm x y (List.finRange m) f

theorem canonicalMatchingCubeOperatorOdd_xor_apply
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x y : Cube m) (f : TableauSpace lam) :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeXor x y) f =
      canonicalMatchingCubeOperatorOdd (lam := lam) x
        (canonicalMatchingCubeOperatorOdd (lam := lam) y f) := by
  let A : Fin m -> TableauSpace lam -> TableauSpace lam :=
    fun r => canonicalMatchingYoungOperatorOdd (lam := lam) r
  have hinv : ∀ r v, A r (A r v) = v := by
    intro r v
    exact canonicalMatchingYoungOperatorOdd_involutive r v
  have hcomm : ∀ r s v, A r (A s v) = A s (A r v) := by
    intro r s v
    by_cases hrs : r = s
    · subst s
      rfl
    · exact canonicalMatchingYoungOperatorOdd_comm hrs v
  rw [canonicalMatchingCubeOperatorOdd_eq_indexedProduct (lam := lam)]
  rw [canonicalMatchingCubeOperatorOdd_eq_indexedProduct (lam := lam) x]
  rw [canonicalMatchingCubeOperatorOdd_eq_indexedProduct (lam := lam) y]
  exact indexedOperatorListProduct_xor_apply
    (A := A) hinv hcomm x y (List.finRange m) f

theorem canonicalMatchingCubeOperatorEven_xor
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorEven (lam := lam) x
        (canonicalMatchingCubeOperatorEven (lam := lam) y f) := by
  funext f
  exact canonicalMatchingCubeOperatorEven_xor_apply x y f

theorem canonicalMatchingCubeOperatorOdd_xor
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorOdd (lam := lam) x
        (canonicalMatchingCubeOperatorOdd (lam := lam) y f) := by
  funext f
  exact canonicalMatchingCubeOperatorOdd_xor_apply x y f

/-- On a simultaneous even matching eigenspace, a cube element acts by the
product of its selected edge signs. -/
theorem canonicalMatchingCubeOperatorEven_apply_of_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f =
      ((List.finRange m).map
        (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod • f := by
  rw [canonicalMatchingCubeOperatorEven_eq_indexedProduct (lam := lam) x]
  exact indexedOperatorListProduct_eigenvector_apply
    (A := fun r : Fin m => canonicalMatchingYoungOperatorEven (lam := lam) r)
    (c := fun r : Fin m => matchingEdgeSign R r) f
    (fun r a => canonicalMatchingYoungOperatorEven_smul r a f)
    hf x (List.finRange m)

/-- On a simultaneous odd matching eigenspace, a cube element acts by the
product of its selected edge signs. -/
theorem canonicalMatchingCubeOperatorOdd_apply_of_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f =
      ((List.finRange m).map
        (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod • f := by
  rw [canonicalMatchingCubeOperatorOdd_eq_indexedProduct (lam := lam) x]
  exact indexedOperatorListProduct_eigenvector_apply
    (A := fun r : Fin m => canonicalMatchingYoungOperatorOdd (lam := lam) r)
    (c := fun r : Fin m => matchingEdgeSign R r) f
    (fun r a => canonicalMatchingYoungOperatorOdd_smul r a f)
    hf x (List.finRange m)

/-- On a simultaneous even matching eigenspace, a cube element acts by the
matching character indexed by that eigenspace. -/
theorem canonicalMatchingCubeOperatorEven_apply_character_of_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f = cubeChar R x • f := by
  rw [canonicalMatchingCubeOperatorEven_apply_of_isMatchingEigenvector hf x]
  rw [matchingEdgeSign_finRange_product_eq_cubeChar R x]

/-- On a simultaneous odd matching eigenspace, a cube element acts by the
matching character indexed by that eigenspace. -/
theorem canonicalMatchingCubeOperatorOdd_apply_character_of_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f = cubeChar R x • f := by
  rw [canonicalMatchingCubeOperatorOdd_apply_of_isMatchingEigenvector hf x]
  rw [matchingEdgeSign_finRange_product_eq_cubeChar R x]

/-- The `+1` projection for one even canonical matching edge. -/
noncomputable def matchingEdgePlusProjectionEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) : TableauSpace lam :=
  (1 / 2 : ℝ) •
    (fun T => f T + canonicalMatchingYoungOperatorEven r f T)

/-- The `-1` projection for one even canonical matching edge. -/
noncomputable def matchingEdgeMinusProjectionEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) : TableauSpace lam :=
  (1 / 2 : ℝ) •
    (fun T => f T - canonicalMatchingYoungOperatorEven r f T)

/-- The `+1` projection for one odd canonical matching edge. -/
noncomputable def matchingEdgePlusProjectionOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) : TableauSpace lam :=
  (1 / 2 : ℝ) •
    (fun T => f T + canonicalMatchingYoungOperatorOdd r f T)

/-- The `-1` projection for one odd canonical matching edge. -/
noncomputable def matchingEdgeMinusProjectionOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) : TableauSpace lam :=
  (1 / 2 : ℝ) •
    (fun T => f T - canonicalMatchingYoungOperatorOdd r f T)

theorem matchingEdgePlusProjectionEven_isPlusEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgePlusProjectionEven r f) =
      matchingEdgePlusProjectionEven r f := by
  unfold matchingEdgePlusProjectionEven
  rw [canonicalMatchingYoungOperatorEven_smul,
    canonicalMatchingYoungOperatorEven_plusEigenVec]

theorem matchingEdgeMinusProjectionEven_isMinusEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgeMinusProjectionEven r f) =
      (-1 : ℝ) • matchingEdgeMinusProjectionEven r f := by
  unfold matchingEdgeMinusProjectionEven
  rw [canonicalMatchingYoungOperatorEven_smul,
    canonicalMatchingYoungOperatorEven_minusEigenVec]
  funext T
  simp [Pi.smul_apply]
  ring

theorem matchingEdgePlusProjectionOdd_isPlusEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgePlusProjectionOdd r f) =
      matchingEdgePlusProjectionOdd r f := by
  unfold matchingEdgePlusProjectionOdd
  rw [canonicalMatchingYoungOperatorOdd_smul,
    canonicalMatchingYoungOperatorOdd_plusEigenVec]

theorem matchingEdgeMinusProjectionOdd_isMinusEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgeMinusProjectionOdd r f) =
      (-1 : ℝ) • matchingEdgeMinusProjectionOdd r f := by
  unfold matchingEdgeMinusProjectionOdd
  rw [canonicalMatchingYoungOperatorOdd_smul,
    canonicalMatchingYoungOperatorOdd_minusEigenVec]
  funext T
  simp [Pi.smul_apply]
  ring

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
