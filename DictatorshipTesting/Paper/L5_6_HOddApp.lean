import DictatorshipTesting.Paper.Aux_HOddFiniteInduction

/-!
# Lemma 5.6: Odd certificate

This is `lem:h-odd-app` from `soda27authors_section5_rethought.tex`.

The odd certificate reduces through one-box branching to the even certificate,
except for two level-two odd shapes.  The detailed finite case analysis is
isolated in `Aux_HOddFiniteInduction`.
-/

namespace DictatorshipTesting

/-- Lemma 5.6, `lem:h-odd-app`: odd certificate. -/
theorem L5_6_HOddApp (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  -- This wrapper makes the dependency of Theorem 4.10 on the odd certificate
  -- explicit while keeping the open finite induction in one place.
  exact
    hOdd_ge_one_sixth_youngDim_of_not_oneRow_not_standard_finite_induction
      m hm lam hrow hstd

end DictatorshipTesting
