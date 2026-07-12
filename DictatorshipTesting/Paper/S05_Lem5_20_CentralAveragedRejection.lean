import DictatorshipTesting.Paper.S05_Lem5_19_LocalTruncationAsConvolution
import DictatorshipTesting.Paper.S04_Prop4_03_MatchingLocalTruncationOrthogonalProjection
import DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_21_BlockScalarOfTheAveragedRejection`
- `DictatorshipTesting.Paper.S05_Lem5_22_GlobalWeightedMatchingIdentity`
-/


/-!
Paper statement: Lemma 5.20 (`lem:averaged-rejection-central`)
Title in paper: Central averaged rejection.

Status: proven finite-average component.  Definition 5.12 constructs the
corresponding group-algebra element and proves its coefficient centrality; the
global block-energy identification remains part of the spectral-model boundary.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.20 finite-average component: the local rejection error is the
square distance from `F` to its matching-local projection. -/
theorem S05_Lem5_20_matchingLocalProjectionError_eq_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq F (matchingLocalProjection M F) := by
  rfl

/-- Lemma 5.20 finite-average component: the local rejection error is the
square norm of the high matching idempotent. -/
theorem S05_Lem5_20_matchingLocalProjectionError_eq_high_idempotent_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq (S05_matchingHighIdempotent M F) (fun _ => 0) := by
  unfold matchingLocalProjectionError l2DistSq
  congr 1
  apply Finset.sum_congr rfl
  intro π _hπ
  have hres := congrFun (S05_Lem5_19_residual_eq_high_idempotent M F) π
  rw [← hres]
  ring

/-- Lemma 5.20 finite-average component: the averaged rejection is the uniform
finite average of local projection errors over near-perfect matchings.  This is
the concrete quantity whose future operator-level refinement is centrality. -/
theorem S05_Lem5_20_matchingMeanProjectionError_eq_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        matchingLocalProjectionError F M.toOrdered) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rfl

/-- Lemma 5.20 finite-average component: the averaged rejection is the uniform
average of the squared high-idempotent norms. -/
theorem S05_Lem5_20_matchingMeanProjectionError_eq_high_idempotent_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        l2DistSq (S05_matchingHighIdempotent M.toOrdered F) (fun _ => 0)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rw [S05_Lem5_20_matchingMeanProjectionError_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro M _hM
  exact S05_Lem5_20_matchingLocalProjectionError_eq_high_idempotent_l2DistSq
    F M.toOrdered


/-- One local projection error is the quadratic form of its concrete high
matching idempotent. -/
theorem matchingLocalProjectionError_eq_permInner_highIdempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      permInner F (S05_matchingHighIdempotent M F) := by
  have hlocal :=
    (S04_Prop4_03_perpendicular F (matchingLocalProjection M F) M
      (S04_Prop4_03_fixedSpace F M).1).2
  rw [S05_Lem5_19_residual_eq_high_idempotent M F] at hlocal
  exact hlocal.symm


end DictatorshipTesting
