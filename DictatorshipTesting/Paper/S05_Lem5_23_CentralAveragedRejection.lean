import DictatorshipTesting.Paper.S05_Lem5_22_LocalTruncationAsConvolution

/-!
Paper statement: Lemma 5.23 (`lem:averaged-rejection-central`)
Title in paper: Central averaged rejection.

Status: paper-facing owner file for the rewritten Section 5 statement.  The
finite-average and high-idempotent norm identities are proved below.  The
centrality proof requires the future group-algebra/Young-block operator API;
the current Lean scaffold keeps the downstream scalar algebra separate.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.23 finite-average component: the local rejection error is the
square distance from `F` to its matching-local projection. -/
theorem S05_Lem5_23_matchingLocalProjectionError_eq_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq F (matchingLocalProjection M F) := by
  rfl

/-- Lemma 5.23 finite-average component: the local rejection error is the
square norm of the high matching idempotent. -/
theorem S05_Lem5_23_matchingLocalProjectionError_eq_high_idempotent_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq (S05_matchingHighIdempotent M F) (fun _ => 0) := by
  unfold matchingLocalProjectionError l2DistSq
  congr 1
  apply Finset.sum_congr rfl
  intro π _hπ
  have hres := congrFun (S05_Lem5_22_residual_eq_high_idempotent M F) π
  rw [← hres]
  ring

/-- Lemma 5.23 finite-average component: the averaged rejection is the uniform
finite average of local projection errors over near-perfect matchings.  This is
the concrete quantity whose future operator-level refinement is centrality. -/
theorem S05_Lem5_23_matchingMeanProjectionError_eq_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        matchingLocalProjectionError F M.toOrdered) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rfl

/-- Lemma 5.23 finite-average component: the averaged rejection is the uniform
average of the squared high-idempotent norms. -/
theorem S05_Lem5_23_matchingMeanProjectionError_eq_high_idempotent_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        l2DistSq (S05_matchingHighIdempotent M.toOrdered F) (fun _ => 0)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rw [S05_Lem5_23_matchingMeanProjectionError_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro M _hM
  exact S05_Lem5_23_matchingLocalProjectionError_eq_high_idempotent_l2DistSq
    F M.toOrdered

end DictatorshipTesting
