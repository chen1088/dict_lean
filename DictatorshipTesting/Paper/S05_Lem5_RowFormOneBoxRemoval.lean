import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-!
Paper statement: Section 5 lemma, `lem:one-box-row-form`
Title in paper: Row form of one-box removals.

This is the paper-facing wrapper for the elementary row-combinatorial fact that
a one-box child differs from its parent in exactly one row.
-/

noncomputable section

namespace DictatorshipTesting

/-- Paper lemma `lem:one-box-row-form`: a one-box child differs from its parent
in exactly one row. -/
theorem S05_oneBox_row_form
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact exists_unique_row_of_oneBoxChild h

end DictatorshipTesting
