import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Size-indexed Young diagrams

This module contains the finite row-vector presentation used by explicit
tableau computations.  Unlike Mathlib's unindexed `YoungDiagram`, the size is
part of the type, so rows and cells have finite coordinate types.

The preferred public name is `IndexedYoungDiagram`.  The shorter
`AlgebraicLibrary.YoungDiagram` is retained as a compatibility alias for the
existing development.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- A Young diagram with `n` boxes, represented by `n` bounded row lengths. -/
structure IndexedYoungDiagram (n : ℕ) where
  row : Fin n → Fin (n + 1)
  nonincreasing :
    ∀ {i j : Fin n}, (i : ℕ) ≤ (j : ℕ) → (row j : ℕ) ≤ (row i : ℕ)
  sum_rows : (∑ i : Fin n, (row i : ℕ)) = n
deriving DecidableEq

/-- Compatibility name for the indexed row-vector presentation. -/
abbrev YoungDiagram := IndexedYoungDiagram

noncomputable instance indexedYoungDiagramFintype (n : ℕ) :
    Fintype (IndexedYoungDiagram n) := by
  classical
  exact Fintype.ofInjective IndexedYoungDiagram.row (by
    intro lam mu h
    cases lam
    cases mu
    simp at h
    simp [h])

namespace IndexedYoungDiagram

/-- The bounded rows as an ordinary list of natural row lengths. -/
def rowLengths {n : ℕ} (lam : IndexedYoungDiagram n) : List ℕ :=
  List.ofFn (fun i => (lam.row i : ℕ))

@[simp] theorem rowLengths_length {n : ℕ} (lam : IndexedYoungDiagram n) :
    lam.rowLengths.length = n := by
  simp [rowLengths]

theorem rowLengths_sorted {n : ℕ} (lam : IndexedYoungDiagram n) :
    lam.rowLengths.SortedGE := by
  apply Antitone.sortedGE_ofFn
  intro i j hij
  apply lam.nonincreasing
  exact hij

/-- Forget the size index and convert to Mathlib's global Young diagram. -/
def toMathlib {n : ℕ} (lam : IndexedYoungDiagram n) :
    _root_.YoungDiagram :=
  _root_.YoungDiagram.ofRowLens lam.rowLengths lam.rowLengths_sorted

/-- The conversion preserves every represented row length. -/
theorem toMathlib_rowLen {n : ℕ} (lam : IndexedYoungDiagram n)
    (i : Fin n) :
    lam.toMathlib.rowLen i = (lam.row i : ℕ) := by
  let i' : Fin lam.rowLengths.length :=
    ⟨i, by simp⟩
  simpa [toMathlib, rowLengths, i'] using
    (_root_.YoungDiagram.rowLen_ofRowLens
      (w := lam.rowLengths) (hw := lam.rowLengths_sorted) i')

end IndexedYoungDiagram

/-- Row length, extended by zero beyond the represented rows. -/
def youngRow {n : ℕ} (lam : IndexedYoungDiagram n) (i : ℕ) : ℕ :=
  if h : i < n then (lam.row ⟨i, h⟩ : ℕ) else 0

theorem youngRow_of_lt {n i : ℕ} (lam : IndexedYoungDiagram n)
    (h : i < n) :
    youngRow lam i = (lam.row ⟨i, h⟩ : ℕ) := by
  simp [youngRow, h]

theorem youngRow_of_not_lt {n i : ℕ}
    (lam : IndexedYoungDiagram n) (h : ¬ i < n) :
    youngRow lam i = 0 := by
  simp [youngRow, h]

theorem youngRow_fin {n : ℕ} (lam : IndexedYoungDiagram n)
    (i : Fin n) :
    youngRow lam i = (lam.row i : ℕ) := by
  simp [youngRow]

/-- Cells as zero-based, finitely bounded row-column pairs. -/
def youngCells {n : ℕ} (lam : IndexedYoungDiagram n) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun cell : Fin n × Fin n =>
    (cell.2 : ℕ) < youngRow lam cell.1)

/-- Hook length of a cell in an indexed Young diagram. -/
def youngHookLength {n : ℕ} (lam : IndexedYoungDiagram n)
    (cell : Fin n × Fin n) : ℕ :=
  (youngRow lam cell.1 - (cell.2 : ℕ)) +
    (Finset.univ.filter (fun r : Fin n =>
      (cell.1 : ℕ) < (r : ℕ) ∧
        (cell.2 : ℕ) < youngRow lam r)).card

/-- Natural-valued hook-length expression. -/
def youngDimNat {n : ℕ} (lam : IndexedYoungDiagram n) : ℕ :=
  Nat.factorial n / (youngCells lam).prod (youngHookLength lam)

/-- Real-valued hook-length expression. -/
def youngDim {n : ℕ} (lam : IndexedYoungDiagram n) : ℝ :=
  youngDimNat lam

/-- Predicate for the one-row diagram. -/
def IsOneRow {n : ℕ} (lam : IndexedYoungDiagram n) : Prop :=
  youngRow lam 0 = n

/-- Predicate for the standard-representation shape `(n - 1, 1)`. -/
def IsStandard {n : ℕ} (lam : IndexedYoungDiagram n) : Prop :=
  2 ≤ n ∧ youngRow lam 0 = n - 1 ∧ youngRow lam 1 = 1

/-- Diagram containment expressed by row lengths. -/
def IsYoungSubdiagram {n k : ℕ} (mu : IndexedYoungDiagram k)
    (lam : IndexedYoungDiagram n) : Prop :=
  ∀ i : Fin n, youngRow mu i ≤ youngRow lam i

/-- `lam / mu` is a horizontal two-strip. -/
def IsHorizontalTwoStripChild {n k : ℕ} (lam : IndexedYoungDiagram n)
    (mu : IndexedYoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam ((i : ℕ) + 1) ≤ youngRow mu i

/-- `lam / mu` is a vertical two-strip. -/
def IsVerticalTwoStripChild {n k : ℕ} (lam : IndexedYoungDiagram n)
    (mu : IndexedYoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam i ≤ youngRow mu i + 1

/-- `lam / mu` consists of one removable cell. -/
def IsOneBoxChild {n k : ℕ} (lam : IndexedYoungDiagram n)
    (mu : IndexedYoungDiagram k) : Prop :=
  k + 1 = n ∧ IsYoungSubdiagram mu lam

/-- Horizontal two-strip children. -/
def horizontalTwoStripChildren {n : ℕ} (lam : IndexedYoungDiagram n) :
    Finset (IndexedYoungDiagram (n - 2)) := by
  classical
  exact Finset.univ.filter (IsHorizontalTwoStripChild lam)

/-- Vertical two-strip children. -/
def verticalTwoStripChildren {n : ℕ} (lam : IndexedYoungDiagram n) :
    Finset (IndexedYoungDiagram (n - 2)) := by
  classical
  exact Finset.univ.filter (IsVerticalTwoStripChild lam)

/-- One-box children. -/
def oneBoxChildren {n : ℕ} (lam : IndexedYoungDiagram n) :
    Finset (IndexedYoungDiagram (n - 1)) := by
  classical
  exact Finset.univ.filter (IsOneBoxChild lam)

/-- Horizontal two-strip children in the even-size parameterization. -/
def horizontalTwoStripChildrenEven (m : ℕ)
    (lam : IndexedYoungDiagram (2 * m)) :
    Finset (IndexedYoungDiagram (2 * (m - 1))) := by
  classical
  exact Finset.univ.filter (IsHorizontalTwoStripChild lam)

/-- Vertical two-strip children in the even-size parameterization. -/
def verticalTwoStripChildrenEven (m : ℕ)
    (lam : IndexedYoungDiagram (2 * m)) :
    Finset (IndexedYoungDiagram (2 * (m - 1))) := by
  classical
  exact Finset.univ.filter (IsVerticalTwoStripChild lam)

/-- One-box children in the odd-to-even parameterization. -/
def oneBoxChildrenOdd (m : ℕ)
    (lam : IndexedYoungDiagram (2 * m + 1)) :
    Finset (IndexedYoungDiagram (2 * m)) := by
  classical
  exact Finset.univ.filter (IsOneBoxChild lam)

end AlgebraicLibrary
