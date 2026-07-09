import DictatorshipTesting.Paper.S05_Lem5_49_OddCertificate

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Lemma 5.48 (`lem:exceptional-odd-children`)
Title in paper: Odd exceptional children.

Status: proven. Paper-facing wrapper around the existing odd exceptional-child
classification theorem.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.38: all failures of the generic odd reduction are among the two
explicit odd exceptional shapes. -/
theorem S05_Lem5_48_odd_exceptional_children
    (m : Nat) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hbad : HasOneRowOneBoxChild m lam ∨ HasStandardOneBoxChild m lam) :
    IsOddHExceptional m lam := by
  exact odd_bad_oneBoxChild_classification m hm lam hrow hstd hbad

end DictatorshipTesting
