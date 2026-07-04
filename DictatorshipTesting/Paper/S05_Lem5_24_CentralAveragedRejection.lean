import DictatorshipTesting.Paper.S05_Lem5_23_LocalTruncationAsConvolution

/-!
Paper statement: Lemma 5.24 (`lem:averaged-rejection-central`)
Title in paper: Central averaged rejection.

Status: paper-facing owner file for the rewritten Section 5 statement.  The
centrality proof requires the future group-algebra/Young-block operator API;
the current Lean scaffold keeps the downstream scalar algebra separate.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.24 finite-average component: the local rejection error is the
square distance from `F` to its matching-local projection. -/
theorem S05_Lem5_24_matchingLocalProjectionError_eq_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq F (matchingLocalProjection M F) := by
  rfl

/-- Lemma 5.24 finite-average component: the averaged rejection is the uniform
finite average of local projection errors over near-perfect matchings.  This is
the concrete quantity whose future operator-level refinement is centrality. -/
theorem S05_Lem5_24_matchingMeanProjectionError_eq_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        matchingLocalProjectionError F M.toOrdered) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rfl

end DictatorshipTesting
