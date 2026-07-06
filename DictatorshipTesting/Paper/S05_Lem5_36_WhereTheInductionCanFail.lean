import DictatorshipTesting.Paper.S05_Lem5_37_EvenCertificate

/-!
Paper statement: Lemma 5.36 (`lem:exceptional-even-children`)
Title in paper: Where the induction can fail.

Status: paper-facing wrapper around the existing even exceptional-child
classification theorem.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.38: all failures of the generic even induction are among the four
explicit exceptional shapes. -/
theorem S05_Lem5_36_where_the_induction_can_fail
    (m : Nat) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hbad :
      HasOneRowHorizontalChild m lam ∨
        HasOneRowVerticalChild m lam ∨
          HasStandardHorizontalChild m lam) :
    IsEvenHExceptional m lam := by
  exact even_bad_child_classification m hm lam hrow hstd hbad

end DictatorshipTesting
