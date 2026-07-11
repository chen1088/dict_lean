import DictatorshipTesting.Paper.S05_Int_TableauDimension

/-!
# Young-tableau square sums

This file develops the rank-generic Young-lattice combinatorics needed to prove
that the sum of the squared numbers of standard tableaux is a factorial.  The
first layer exposes one-box lower and upper covers and restates the existing
tableau-deletion recursion over natural numbers.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The Young diagrams obtained by deleting one box from `lam`. -/
def youngLowerCovers {n : Nat} (lam : YoungDiagram (n + 1)) :
    Finset (YoungDiagram n) :=
  oneBoxChildrenSized lam

/-- The Young diagrams obtained by adding one box to `mu`. -/
def youngUpperCovers {n : Nat} (mu : YoungDiagram n) :
    Finset (YoungDiagram (n + 1)) := by
  classical
  exact Finset.univ.filter (fun lam : YoungDiagram (n + 1) =>
    IsOneBoxChild lam mu)

@[simp] theorem mem_youngLowerCovers_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n} :
    mu ∈ youngLowerCovers lam ↔ IsOneBoxChild lam mu := by
  simp [youngLowerCovers, mem_oneBoxChildrenSized_iff]

@[simp] theorem mem_youngUpperCovers_iff {n : Nat}
    {mu : YoungDiagram n} {lam : YoungDiagram (n + 1)} :
    lam ∈ youngUpperCovers mu ↔ IsOneBoxChild lam mu := by
  simp [youngUpperCovers]

theorem mem_youngLowerCovers_iff_mem_youngUpperCovers {n : Nat}
    {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n} :
    mu ∈ youngLowerCovers lam ↔ lam ∈ youngUpperCovers mu := by
  simp

/-- Natural-number form of the generic one-box tableau-deletion recursion. -/
theorem tableauDimNat_eq_sum_lowerCovers {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    tableauDimNat lam =
      (youngLowerCovers lam).sum (fun mu => tableauDimNat mu) := by
  classical
  rw [tableauDimNat_eq_card]
  rw [card_standardYoungTableau_eq_sum_removableRow_children lam]
  change
    (∑ r : RemovableRow lam,
      tableauDimNat (removableRowToOneBoxChild lam r)) =
      (youngLowerCovers lam).sum (fun mu => tableauDimNat mu)
  have hsum_subtype :
      (∑ mu : {mu : YoungDiagram n // mu ∈ youngLowerCovers lam},
        tableauDimNat mu.1) =
        (youngLowerCovers lam).sum (fun mu => tableauDimNat mu) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (youngLowerCovers lam) (fun mu => tableauDimNat mu)
  exact (Fintype.sum_equiv
    (removableRowsEquivOneBoxChildren lam)
    (fun r : RemovableRow lam =>
      tableauDimNat (removableRowToOneBoxChild lam r))
    (fun mu : {mu : YoungDiagram n // mu ∈ youngLowerCovers lam} =>
      tableauDimNat mu.1)
    (fun _ => rfl)).trans hsum_subtype

end DictatorshipTesting
