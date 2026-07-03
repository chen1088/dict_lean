import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-!
Paper statement: Section 5 lemma, `lem:one-box-removable-row`
Title in paper: One-box removals delete a removable row.

This is an elementary row-combinatorial wrapper for the statement that if
`mu` is a one-box child of `lambda`, then the deleted box lies at the end of
a removable row of `lambda`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Paper lemma `lem:one-box-removable-row`: a one-box child removes the final
box of a removable row of the parent. -/
theorem S05_oneBox_removable_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact exists_removableRow_of_oneBoxChild h

end DictatorshipTesting
