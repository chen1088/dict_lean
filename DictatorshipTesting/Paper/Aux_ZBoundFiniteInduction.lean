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

/-- A diagram has a horizontal two-strip child that is the one-row diagram.  This
is the exact obstruction to applying the induction hypothesis uniformly to all
horizontal children in the proof of the `zEven` bound. -/
def HasOneRowHorizontalChild (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  ∃ mu ∈ horizontalTwoStripChildrenEven m lam, IsOneRow mu

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

/-- Two-strip dimension recursion for the hook-length dimension.

This is the finite combinatorial identity
`d_lambda = sum_{horizontal children} d_mu + sum_{vertical children} d_mu`.
It is the main missing hook-length/branching calculation needed by the generic
induction step. -/
theorem youngDim_twoStrip_recurrence (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
  sorry

/-- The horizontal part of the two-strip dimension recursion is bounded by the
full dimension. -/
theorem youngDim_horizontalChildren_sum_le (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) ≤
      youngDim lam := by
  have hrec := youngDim_twoStrip_recurrence m hm lam
  have hv_nonneg :
      0 ≤ (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
    exact Finset.sum_nonneg (fun mu _hmu => youngDim_nonneg mu)
  linarith

/-- Base case for the finite `zEven` induction at `m = 1`.

There is only one non-one-row diagram of size two, namely `(1,1)`, and its
horizontal two-strip child set is empty. -/
theorem zEven_le_half_youngDim_m_one
    (lam : YoungDiagram (2 * 1)) (hrow : ¬ IsOneRow lam) :
    zEven 1 lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  classical
  have hrow1pos : 0 < youngRow lam 1 := by
    unfold IsOneRow youngRow at hrow
    simp at hrow
    unfold youngRow
    simp
    have hsum : (lam.row 0 : ℕ) + (lam.row 1 : ℕ) = 2 := by
      simpa using lam.sum_rows
    have h0ne : ¬ (lam.row 0 : ℕ) = 2 := by
      exact hrow
    omega
  have hz : zEven 1 lam = 0 := by
    change (horizontalTwoStripChildrenEven 1 lam).sum
      (fun mu => zEven 0 mu) = 0
    apply Finset.sum_eq_zero
    intro mu hmu
    have hstrip : IsHorizontalTwoStripChild lam mu :=
      (Finset.mem_filter.mp hmu).2
    have hle := hstrip.2.2 (0 : Fin (2 * 1))
    have hmu0 : youngRow mu 0 = 0 := by
      unfold youngRow
      simp
    have hzle : youngRow lam 1 ≤ 0 := by
      simpa [hmu0] using hle
    omega
  rw [hz]
  exact mul_nonneg (by norm_num) (youngDim_nonneg lam)

/-- Exceptional case for the finite `zEven` induction.

If a non-one-row diagram has a one-row horizontal child, the paper's proof
classifies it as one of the two explicit families `(2m-1,1)` or `(2m-2,2)`
and checks the hook-length formulas directly.  That finite classification and
calculation is isolated here. -/
theorem zEven_le_half_youngDim_of_hasOneRowHorizontalChild
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hchild : HasOneRowHorizontalChild m lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  sorry

/-- Generic induction step for the `zEven` bound, away from the one-row-child
exceptions. -/
theorem zEven_le_half_youngDim_of_noOneRowHorizontalChild
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (ih :
      ∀ mu : YoungDiagram (2 * (m - 1)),
        ¬ IsOneRow mu →
          zEven (m - 1) mu ≤ (1 / 2 : ℝ) * youngDim mu)
    (hno : ¬ HasOneRowHorizontalChild m lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  have hzrec := zEven_horizontal_recurrence m (by omega) lam
  rw [hzrec]
  have hchild_nonrow :
      ∀ mu ∈ horizontalTwoStripChildrenEven m lam, ¬ IsOneRow mu := by
    intro mu hmu hone
    exact hno ⟨mu, hmu, hone⟩
  have hsum_ind :
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => zEven (m - 1) mu) ≤
        (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => (1 / 2 : ℝ) * youngDim mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    exact ih mu (hchild_nonrow mu hmu)
  have hsum_dim :
      (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => (1 / 2 : ℝ) * youngDim mu) =
        (1 / 2 : ℝ) *
          (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
    rw [Finset.mul_sum]
  have hdim_le :
      (1 / 2 : ℝ) *
          (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) ≤
        (1 / 2 : ℝ) * youngDim lam := by
    exact mul_le_mul_of_nonneg_left
      (youngDim_horizontalChildren_sum_le m hm lam) (by norm_num)
  linarith

/-- Finite Young-diagram induction behind Lemma 5.4. -/
theorem zEven_le_half_youngDim_of_not_oneRow_finite_induction
    (m : ℕ) (lam : YoungDiagram (2 * m)) (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  induction m with
  | zero =>
      have hone : IsOneRow lam := by
        unfold IsOneRow youngRow
        simp
      exact False.elim (hrow hone)
  | succ m ih =>
      cases m with
      | zero =>
          exact zEven_le_half_youngDim_m_one lam hrow
      | succ m =>
          by_cases hchild : HasOneRowHorizontalChild (Nat.succ (Nat.succ m)) lam
          · exact zEven_le_half_youngDim_of_hasOneRowHorizontalChild
              (Nat.succ (Nat.succ m)) (by omega) lam hrow hchild
          · exact zEven_le_half_youngDim_of_noOneRowHorizontalChild
              (Nat.succ (Nat.succ m)) (by omega) lam ih hchild

end DictatorshipTesting
