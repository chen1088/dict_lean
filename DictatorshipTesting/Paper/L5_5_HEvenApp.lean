import DictatorshipTesting.Paper.Aux_HEvenFiniteInduction

/-!
# Lemma 5.5: Even certificate

This is `lem:h-even-app` from `soda27authors_section5_rethought.tex`.

The proof in the paper is an induction using Lemma 5.4 and then four explicit
exceptional Young-diagram families.  That finite induction is factored into
`Aux_HEvenFiniteInduction`; this file records the paper-numbered interface.
-/

namespace DictatorshipTesting

/-- Lemma 5.5, `lem:h-even-app`: even certificate. -/
theorem L5_5_HEvenApp (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  -- Keep the numbered lemma as the stable API for Theorem 4.10.
  exact
    hEven_ge_one_fifth_youngDim_of_not_oneRow_not_standard_finite_induction
      m hm lam hrow hstd

end DictatorshipTesting
