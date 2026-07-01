import DictatorshipTesting.Paper.Aux_ZBoundFiniteInduction

/-!
# Lemma 5.4: Weight-zero entries are never a majority

This is `lem:z-bound-app` from `soda27authors_section5_rethought.tex`.

The numbered lemma is kept small on purpose.  The remaining proof is the finite
Young-diagram induction in `Aux_ZBoundFiniteInduction`: it needs the horizontal
two-strip recurrence, the dimension recursion, and the special shapes
`(2m-1,1)` and `(2m-2,2)`.
-/

namespace DictatorshipTesting

/-- Lemma 5.4, `lem:z-bound-app`: weight-zero entries are never a majority. -/
theorem L5_4_ZBoundApp (m : ℕ) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  -- The hard combinatorial induction is isolated with a descriptive name so
  -- downstream files can depend on Lemma 5.4 without hiding the open work.
  exact zEven_le_half_youngDim_of_not_oneRow_finite_induction m lam hrow

end DictatorshipTesting
