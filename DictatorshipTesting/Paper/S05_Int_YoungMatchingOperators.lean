import AlgebraicLibrary.Young.OrthogonalRepresentation
import AlgebraicLibrary.BooleanCube.Fourier
import AlgebraicLibrary.BooleanCube.Basic
import AlgebraicLibrary.Algebra.OperatorProduct

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_13_MatchingSubgroupEigenbasis`
-/
/-!
# Canonical matching operators in Young coordinates

This internal Section 5 module packages the elementary operator algebra for the canonical matching
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

theorem canonicalMatchingYoungOperatorEven_add
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f g : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r (fun T => f T + g T) =
      fun T => canonicalMatchingYoungOperatorEven r f T +
        canonicalMatchingYoungOperatorEven r g T := by
  unfold canonicalMatchingYoungOperatorEven
  exact youngAdjacentOperator_add (canonicalMatchingAdjacentIndex m r) f g

theorem canonicalMatchingYoungOperatorOdd_add
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f g : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r (fun T => f T + g T) =
      fun T => canonicalMatchingYoungOperatorOdd r f T +
        canonicalMatchingYoungOperatorOdd r g T := by
  unfold canonicalMatchingYoungOperatorOdd
  exact youngAdjacentOperator_add (canonicalNearMatchingAdjacentIndex m r) f g

theorem canonicalMatchingYoungOperatorEven_sub
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f g : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r (fun T => f T - g T) =
      fun T => canonicalMatchingYoungOperatorEven r f T -
        canonicalMatchingYoungOperatorEven r g T := by
  unfold canonicalMatchingYoungOperatorEven
  rw [show (fun T => f T - g T) =
      (fun T => f T + (fun U => -g U) T) by
        funext T
        ring]
  rw [youngAdjacentOperator_add, youngAdjacentOperator_neg]
  rfl

theorem canonicalMatchingYoungOperatorOdd_sub
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f g : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r (fun T => f T - g T) =
      fun T => canonicalMatchingYoungOperatorOdd r f T -
        canonicalMatchingYoungOperatorOdd r g T := by
  unfold canonicalMatchingYoungOperatorOdd
  rw [show (fun T => f T - g T) =
      (fun T => f T + (fun U => -g U) T) by
        funext T
        ring]
  rw [youngAdjacentOperator_add, youngAdjacentOperator_neg]
  rfl

/-- The sign of one matching-cube edge for a character support. -/
def matchingEdgeSign {m : Nat} (R : Finset (Fin m)) (r : Fin m) : ℝ :=
  if r ∈ R then -1 else 1

/-- The fixed-order product of selected edge signs is the matching-cube
character with the same support. -/
theorem matchingEdgeSign_finRange_product_eq_cubeChar
    {m : Nat} (R : Finset (Fin m)) (x : FinCube m) :
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
    (x : FinCube m) (r : Fin m) : TableauSpace lam -> TableauSpace lam :=
  if x r then canonicalMatchingYoungOperatorEven r else id

/-- The edge operator selected by one cube bit in the odd case. -/
noncomputable def canonicalMatchingYoungOperatorOddBit
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : FinCube m) (r : Fin m) : TableauSpace lam -> TableauSpace lam :=
  if x r then canonicalMatchingYoungOperatorOdd r else id

/-- Fixed-order product action of the canonical matching cube in the even case. -/
noncomputable def canonicalMatchingCubeOperatorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : FinCube m) : TableauSpace lam -> TableauSpace lam :=
  composeOperatorList
    (List.ofFn fun r : Fin m =>
      canonicalMatchingYoungOperatorEvenBit (lam := lam) x r)

/-- Fixed-order product action of the canonical matching cube in the odd case. -/
noncomputable def canonicalMatchingCubeOperatorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : FinCube m) : TableauSpace lam -> TableauSpace lam :=
  composeOperatorList
    (List.ofFn fun r : Fin m =>
      canonicalMatchingYoungOperatorOddBit (lam := lam) x r)

theorem canonicalMatchingCubeOperatorEven_zero
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)} :
    canonicalMatchingCubeOperatorEven (lam := lam) (finCubeZero m) = id := by
  rw [canonicalMatchingCubeOperatorEven]
  rw [show
      (List.ofFn fun r : Fin m =>
        canonicalMatchingYoungOperatorEvenBit (lam := lam) (finCubeZero m) r) =
        List.ofFn (fun _ : Fin m => (id : TableauSpace lam -> TableauSpace lam)) by
        simp [canonicalMatchingYoungOperatorEvenBit, finCubeZero]]
  rw [List.ofFn_const]
  exact composeOperatorList_replicate_id m

theorem canonicalMatchingCubeOperatorOdd_zero
    {m : Nat} {lam : YoungDiagram (2 * m + 1)} :
    canonicalMatchingCubeOperatorOdd (lam := lam) (finCubeZero m) = id := by
  rw [canonicalMatchingCubeOperatorOdd]
  rw [show
      (List.ofFn fun r : Fin m =>
        canonicalMatchingYoungOperatorOddBit (lam := lam) (finCubeZero m) r) =
        List.ofFn (fun _ : Fin m => (id : TableauSpace lam -> TableauSpace lam)) by
        simp [canonicalMatchingYoungOperatorOddBit, finCubeZero]]
  rw [List.ofFn_const]
  exact composeOperatorList_replicate_id m

theorem canonicalMatchingCubeOperatorEven_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : FinCube m) :
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
    (x : FinCube m) :
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
    (x y : FinCube m) (f : TableauSpace lam) :
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
    (x y : FinCube m) (f : TableauSpace lam) :
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
    (x y : FinCube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorEven (lam := lam) x
        (canonicalMatchingCubeOperatorEven (lam := lam) y f) := by
  funext f
  exact canonicalMatchingCubeOperatorEven_xor_apply x y f

theorem canonicalMatchingCubeOperatorOdd_xor
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x y : FinCube m) :
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
    (hf : IsMatchingEigenvectorEven f R) (x : FinCube m) :
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
    (hf : IsMatchingEigenvectorOdd f R) (x : FinCube m) :
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
    (hf : IsMatchingEigenvectorEven f R) (x : FinCube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f = cubeChar R x • f := by
  rw [canonicalMatchingCubeOperatorEven_apply_of_isMatchingEigenvector hf x]
  rw [matchingEdgeSign_finRange_product_eq_cubeChar R x]

/-- On a simultaneous odd matching eigenspace, a cube element acts by the
matching character indexed by that eigenspace. -/
theorem canonicalMatchingCubeOperatorOdd_apply_character_of_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : IsMatchingEigenvectorOdd f R) (x : FinCube m) :
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

theorem matchingEdgePlusProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s (matchingEdgePlusProjectionEven r f) =
      c • matchingEdgePlusProjectionEven r f := by
  unfold matchingEdgePlusProjectionEven
  rw [canonicalMatchingYoungOperatorEven_smul,
    canonicalMatchingYoungOperatorEven_add, hf,
    canonicalMatchingYoungOperatorEven_comm (r := s) (s := r) (Ne.symm hrs) f,
    hf, canonicalMatchingYoungOperatorEven_smul]
  funext T
  simp [Pi.smul_apply]
  ring

theorem matchingEdgeMinusProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s (matchingEdgeMinusProjectionEven r f) =
      c • matchingEdgeMinusProjectionEven r f := by
  unfold matchingEdgeMinusProjectionEven
  rw [canonicalMatchingYoungOperatorEven_smul,
    canonicalMatchingYoungOperatorEven_sub, hf,
    canonicalMatchingYoungOperatorEven_comm (r := s) (s := r) (Ne.symm hrs) f,
    hf, canonicalMatchingYoungOperatorEven_smul]
  funext T
  simp [Pi.smul_apply]
  ring

theorem matchingEdgePlusProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s (matchingEdgePlusProjectionOdd r f) =
      c • matchingEdgePlusProjectionOdd r f := by
  unfold matchingEdgePlusProjectionOdd
  rw [canonicalMatchingYoungOperatorOdd_smul,
    canonicalMatchingYoungOperatorOdd_add, hf,
    canonicalMatchingYoungOperatorOdd_comm (r := s) (s := r) (Ne.symm hrs) f,
    hf, canonicalMatchingYoungOperatorOdd_smul]
  funext T
  simp [Pi.smul_apply]
  ring

theorem matchingEdgeMinusProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s (matchingEdgeMinusProjectionOdd r f) =
      c • matchingEdgeMinusProjectionOdd r f := by
  unfold matchingEdgeMinusProjectionOdd
  rw [canonicalMatchingYoungOperatorOdd_smul,
    canonicalMatchingYoungOperatorOdd_sub, hf,
    canonicalMatchingYoungOperatorOdd_comm (r := s) (s := r) (Ne.symm hrs) f,
    hf, canonicalMatchingYoungOperatorOdd_smul]
  funext T
  simp [Pi.smul_apply]
  ring

/-- The one-edge even projection selected by a matching-character support:
minus if the edge is in the support and plus otherwise. -/
noncomputable def matchingEdgeSignProjectionEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (r : Fin m)
    (f : TableauSpace lam) : TableauSpace lam :=
  if r ∈ R then
    matchingEdgeMinusProjectionEven r f
  else
    matchingEdgePlusProjectionEven r f

/-- The one-edge odd projection selected by a matching-character support:
minus if the edge is in the support and plus otherwise. -/
noncomputable def matchingEdgeSignProjectionOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (r : Fin m)
    (f : TableauSpace lam) : TableauSpace lam :=
  if r ∈ R then
    matchingEdgeMinusProjectionOdd r f
  else
    matchingEdgePlusProjectionOdd r f

theorem matchingEdgeSignProjectionEven_isMatchingEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgeSignProjectionEven R r f) =
      matchingEdgeSign R r • matchingEdgeSignProjectionEven R r f := by
  unfold matchingEdgeSignProjectionEven matchingEdgeSign
  by_cases hr : r ∈ R
  · simp [hr, matchingEdgeMinusProjectionEven_isMinusEigen r f]
  · simp [hr, matchingEdgePlusProjectionEven_isPlusEigen r f]

theorem matchingEdgeSignProjectionOdd_isMatchingEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgeSignProjectionOdd R r f) =
      matchingEdgeSign R r • matchingEdgeSignProjectionOdd R r f := by
  unfold matchingEdgeSignProjectionOdd matchingEdgeSign
  by_cases hr : r ∈ R
  · simp [hr, matchingEdgeMinusProjectionOdd_isMinusEigen r f]
  · simp [hr, matchingEdgePlusProjectionOdd_isPlusEigen r f]

theorem matchingEdgeSignProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) {r s : Fin m} (hrs : r ≠ s)
    {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s
        (matchingEdgeSignProjectionEven R r f) =
      c • matchingEdgeSignProjectionEven R r f := by
  unfold matchingEdgeSignProjectionEven
  by_cases hr : r ∈ R
  · simp [hr]
    exact matchingEdgeMinusProjectionEven_preserves_otherEigen hrs hf
  · simp [hr]
    exact matchingEdgePlusProjectionEven_preserves_otherEigen hrs hf

theorem matchingEdgeSignProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) {r s : Fin m} (hrs : r ≠ s)
    {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s
        (matchingEdgeSignProjectionOdd R r f) =
      c • matchingEdgeSignProjectionOdd R r f := by
  unfold matchingEdgeSignProjectionOdd
  by_cases hr : r ∈ R
  · simp [hr]
    exact matchingEdgeMinusProjectionOdd_preserves_otherEigen hrs hf
  · simp [hr]
    exact matchingEdgePlusProjectionOdd_preserves_otherEigen hrs hf

/-- Iterated even sign projection along a finite edge list. -/
noncomputable def matchingSignProjectionEvenList
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) : List (Fin m) -> TableauSpace lam -> TableauSpace lam
  | [], f => f
  | r :: rs, f =>
      matchingEdgeSignProjectionEven R r
        (matchingSignProjectionEvenList R rs f)

/-- Iterated odd sign projection along a finite edge list. -/
noncomputable def matchingSignProjectionOddList
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) : List (Fin m) -> TableauSpace lam -> TableauSpace lam
  | [], f => f
  | r :: rs, f =>
      matchingEdgeSignProjectionOdd R r
        (matchingSignProjectionOddList R rs f)

theorem matchingSignProjectionEvenList_isEigen_of_mem
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) {L : List (Fin m)}
    (hnd : L.Nodup) {s : Fin m} (hs : s ∈ L)
    (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven s
        (matchingSignProjectionEvenList R L f) =
      matchingEdgeSign R s • matchingSignProjectionEvenList R L f := by
  induction L generalizing s with
  | nil =>
      cases hs
  | cons r rs ih =>
      have hnd_tail : rs.Nodup := (List.nodup_cons.mp hnd).2
      have hr_not_mem : r ∉ rs := (List.nodup_cons.mp hnd).1
      rcases List.mem_cons.mp hs with hsr | hs_tail
      · subst s
        exact matchingEdgeSignProjectionEven_isMatchingEigen R r
          (matchingSignProjectionEvenList R rs f)
      · have hrs : r ≠ s := by
          intro h
          subst s
          exact hr_not_mem hs_tail
        exact matchingEdgeSignProjectionEven_preserves_otherEigen
          R hrs (ih hnd_tail hs_tail)

theorem matchingSignProjectionOddList_isEigen_of_mem
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) {L : List (Fin m)}
    (hnd : L.Nodup) {s : Fin m} (hs : s ∈ L)
    (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd s
        (matchingSignProjectionOddList R L f) =
      matchingEdgeSign R s • matchingSignProjectionOddList R L f := by
  induction L generalizing s with
  | nil =>
      cases hs
  | cons r rs ih =>
      have hnd_tail : rs.Nodup := (List.nodup_cons.mp hnd).2
      have hr_not_mem : r ∉ rs := (List.nodup_cons.mp hnd).1
      rcases List.mem_cons.mp hs with hsr | hs_tail
      · subst s
        exact matchingEdgeSignProjectionOdd_isMatchingEigen R r
          (matchingSignProjectionOddList R rs f)
      · have hrs : r ≠ s := by
          intro h
          subst s
          exact hr_not_mem hs_tail
        exact matchingEdgeSignProjectionOdd_preserves_otherEigen
          R hrs (ih hnd_tail hs_tail)

/-- Simultaneous even sign projection over all canonical matching edges. -/
noncomputable def matchingSignProjectionEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) : TableauSpace lam :=
  matchingSignProjectionEvenList R (List.finRange m) f

/-- Simultaneous odd sign projection over all canonical matching edges. -/
noncomputable def matchingSignProjectionOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) : TableauSpace lam :=
  matchingSignProjectionOddList R (List.finRange m) f

theorem matchingSignProjectionEven_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) :
    IsMatchingEigenvectorEven (matchingSignProjectionEven R f) R := by
  intro s
  unfold matchingSignProjectionEven
  exact matchingSignProjectionEvenList_isEigen_of_mem R
    (List.nodup_finRange m) (by simp [List.mem_finRange]) f

theorem matchingSignProjectionOdd_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) :
    IsMatchingEigenvectorOdd (matchingSignProjectionOdd R f) R := by
  intro s
  unfold matchingSignProjectionOdd
  exact matchingSignProjectionOddList_isEigen_of_mem R
    (List.nodup_finRange m) (by simp [List.mem_finRange]) f

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
