import DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate

/-
Direct reverse imports:
- None.
-/


/-!
Internal exceptional-parent classification extracted from the proof of
Lemma 5.25.
-/

noncomputable section

namespace DictatorshipTesting

/-- All failures of the generic even induction are among the four
explicit exceptional shapes. -/
theorem S05_whereInductionCanFail
    (m : Nat) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hbad :
      HasOneRowHorizontalChild m lam ∨
        HasOneRowVerticalChild m lam ∨
          HasStandardHorizontalChild m lam) :
    IsEvenHExceptional m lam := by
  exact even_bad_child_classification m hm lam hrow hstd hbad

end DictatorshipTesting
