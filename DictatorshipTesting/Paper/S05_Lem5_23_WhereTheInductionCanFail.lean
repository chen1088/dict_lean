import DictatorshipTesting.Paper.S05_Lem5_24_EvenCertificate

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Lemma 5.23 (`lem:exceptional-even-children`)
Title in paper: Where the induction can fail.

Status: proven. Paper-facing wrapper around the existing even exceptional-child
classification theorem.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.14: all failures of the generic even induction are among the four
explicit exceptional shapes. -/
theorem S05_Lem5_23_where_the_induction_can_fail
    (m : Nat) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hbad :
      HasOneRowHorizontalChild m lam ∨
        HasOneRowVerticalChild m lam ∨
          HasStandardHorizontalChild m lam) :
    IsEvenHExceptional m lam := by
  exact even_bad_child_classification m hm lam hrow hstd hbad

end DictatorshipTesting
