import DictatorshipTesting.Paper.Defs

/-!
# Finite induction input for Lemma 5.4

The paper proves this by induction on `m`, using the horizontal two-strip
recurrence, the dimension recursion, and two special families of diagrams.

This file is the intended home for that proof.  It is separated from
`L5_4_ZBoundApp` so the paper-numbered file remains a concise statement of the
lemma while the eventual proof can accumulate the necessary Young-diagram
bookkeeping lemmas locally.
-/

namespace DictatorshipTesting

/-- Specht dimensions are nonnegative in the concrete hook-length model. -/
theorem youngDim_nonneg {n : ℕ} (lam : YoungDiagram n) :
    0 ≤ youngDim lam := by
  unfold youngDim
  exact_mod_cast Nat.zero_le (youngDimNat lam)

/-- The zero-weight count is nonnegative.  This is the easy positivity part of
the finite induction for Lemma 5.4. -/
theorem zEven_nonneg (m : ℕ) (lam : YoungDiagram (2 * m)) :
    0 ≤ zEven m lam := by
  induction m with
  | zero =>
      simp [zEven]
  | succ m ih =>
      simp [zEven, Finset.sum_nonneg, ih]

/-- The horizontal two-strip recurrence for `zEven`, separated out for the
finite induction. -/
theorem zEven_horizontal_recurrence (m : ℕ) (hm : 1 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    zEven m lam =
      (horizontalTwoStripChildrenEven m lam).sum
        (fun mu => zEven (m - 1) mu) := by
  cases m with
  | zero =>
      omega
  | succ m =>
      simp [zEven]

/-- Finite Young-diagram induction behind Lemma 5.4. -/
theorem zEven_le_half_youngDim_of_not_oneRow_finite_induction
    (m : ℕ) (lam : YoungDiagram (2 * m)) (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  -- TODO: formalize the induction from the paper:
  --   * unfold the horizontal recurrence for `zEven`;
  --   * use the dimension recursion for horizontal two-strip children;
  --   * classify the shapes with a one-row horizontal child;
  --   * compute the standard and `(2m-2,2)` exceptional families.
  sorry

end DictatorshipTesting
