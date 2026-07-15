import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Real.Basic

/-!
# Products of indexed operators

Fixed-order products of Boolean-selected commuting involutions.
-/

namespace AlgebraicLibrary

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

end AlgebraicLibrary
