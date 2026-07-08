import DictatorshipTesting.Paper.Defs

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Lem4_13_OneTrialSoundness`
-/

/-!
# Boolean rejection-probability bridge

This packages the elementary pointwise fact that a Boolean four-query
alternating sum lies in `{-2,-1,0,1,2}`, so its square is at most four times the
indicator of rejection.
-/

noncomputable section

namespace DictatorshipTesting

/-- The Boolean and real-valued trial deltas agree after coercing the Boolean
function to `{0,1}` reals. -/
theorem matchingTrialDeltaReal_boolFnToReal {n : ℕ} (f : BoolFn (Fin n))
    (M : OrderedMatching (Fin n)) (π : Perm (Fin n))
    (c : CubeDirectionColor M.edgeCount) :
    matchingTrialDeltaReal (boolFnToReal f) M π c = matchingTrialDelta f M π c := by
  rfl

/-- Pointwise Boolean bound behind the rejection-probability estimate. -/
theorem bool_four_query_delta_sq_le_indicator (a b c d : Bool) :
    (boolToReal a - boolToReal b - boolToReal c + boolToReal d) ^ (2 : ℕ) ≤
      4 * (if boolToReal a - boolToReal b - boolToReal c + boolToReal d = 0
        then (0 : ℝ) else 1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [boolToReal]

/-- Pointwise version for a matching-cube trial. -/
theorem matchingTrialDelta_sq_le_four_rejectIndicator {n : ℕ}
    (f : BoolFn (Fin n)) (M : OrderedMatching (Fin n)) (π : Perm (Fin n))
    (c : CubeDirectionColor M.edgeCount) :
    (matchingTrialDeltaReal (boolFnToReal f) M π c) ^ (2 : ℕ) ≤
      4 * (if matchingTrialDelta f M π c = 0 then (0 : ℝ) else 1) := by
  unfold matchingTrialDeltaReal matchingTrialDelta cubeDelta matchingCubeRestriction
  exact bool_four_query_delta_sq_le_indicator
    (f (π * M.tau (cubeZero M.edgeCount)))
    (f (π * M.tau (cubeXor (cubeZero M.edgeCount) (cubeColorU c))))
    (f (π * M.tau (cubeXor (cubeZero M.edgeCount) (cubeColorV c))))
    (f (π * M.tau
      (cubeXor (cubeXor (cubeZero M.edgeCount) (cubeColorU c)) (cubeColorV c))))

/-- For Boolean inputs, one-trial rejection probability controls one quarter of
the delta-square expectation. -/
theorem oneTrialRejectProbability_ge_deltaSqExpectation
    (n : ℕ) (f : BoolFn (Fin n)) :
    (1 / 4 : ℝ) * oneTrialDeltaSqExpectation (boolFnToReal f) ≤
      oneTrialRejectProbability f := by
  classical
  unfold oneTrialDeltaSqExpectation oneTrialRejectProbability
  have hCpos : 0 < (Fintype.card (CubeDirectionColor (n / 2)) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos : 0 < Fintype.card (CubeDirectionColor (n / 2)))
  have hPpos : 0 < (Fintype.card (Perm (Fin n)) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Perm (Fin n)))
  have hMpos : 0 < (Fintype.card (NearPerfectMatching n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (NearPerfectMatching n))
  calc
    (1 / 4 : ℝ) *
        ((∑ M : NearPerfectMatching n,
          (∑ π : Perm (Fin n),
            (∑ c : CubeDirectionColor (n / 2),
              (matchingTrialDeltaReal (boolFnToReal f) M.toOrdered π c) ^
                (2 : ℕ)) /
              (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
            (Fintype.card (Perm (Fin n)) : ℝ)) /
          (Fintype.card (NearPerfectMatching n) : ℝ))
        =
        (∑ M : NearPerfectMatching n,
          (1 / 4 : ℝ) *
            ((∑ π : Perm (Fin n),
              (∑ c : CubeDirectionColor (n / 2),
                (matchingTrialDeltaReal (boolFnToReal f) M.toOrdered π c) ^
                  (2 : ℕ)) /
                (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
              (Fintype.card (Perm (Fin n)) : ℝ))) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤
        (∑ M : NearPerfectMatching n,
          (∑ π : Perm (Fin n),
            (∑ c : CubeDirectionColor (n / 2),
              if matchingTrialDelta f M.toOrdered π c = 0 then (0 : ℝ) else 1) /
              (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
            (Fintype.card (Perm (Fin n)) : ℝ)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
          apply div_le_div_of_nonneg_right ?_ (le_of_lt hMpos)
          apply Finset.sum_le_sum
          intro M _hM
          calc
            (1 / 4 : ℝ) *
                ((∑ π : Perm (Fin n),
                  (∑ c : CubeDirectionColor (n / 2),
                    (matchingTrialDeltaReal (boolFnToReal f) M.toOrdered π c) ^
                      (2 : ℕ)) /
                    (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
                  (Fintype.card (Perm (Fin n)) : ℝ))
                =
                (∑ π : Perm (Fin n),
                  (1 / 4 : ℝ) *
                    ((∑ c : CubeDirectionColor (n / 2),
                      (matchingTrialDeltaReal (boolFnToReal f) M.toOrdered π c) ^
                        (2 : ℕ)) /
                      (Fintype.card (CubeDirectionColor (n / 2)) : ℝ))) /
                  (Fintype.card (Perm (Fin n)) : ℝ) := by
                  rw [← Finset.mul_sum]
                  ring
            _ ≤
                (∑ π : Perm (Fin n),
                  (∑ c : CubeDirectionColor (n / 2),
                    if matchingTrialDelta f M.toOrdered π c = 0 then (0 : ℝ) else 1) /
                    (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
                  (Fintype.card (Perm (Fin n)) : ℝ) := by
                  apply div_le_div_of_nonneg_right ?_ (le_of_lt hPpos)
                  apply Finset.sum_le_sum
                  intro π _hπ
                  calc
                    (1 / 4 : ℝ) *
                        ((∑ c : CubeDirectionColor (n / 2),
                          (matchingTrialDeltaReal (boolFnToReal f) M.toOrdered π c) ^
                            (2 : ℕ)) /
                          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ))
                        =
                        (∑ c : CubeDirectionColor (n / 2),
                          (1 / 4 : ℝ) *
                            (matchingTrialDeltaReal (boolFnToReal f)
                              M.toOrdered π c) ^ (2 : ℕ)) /
                          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ) := by
                          rw [← Finset.mul_sum]
                          ring
                    _ ≤
                        (∑ c : CubeDirectionColor (n / 2),
                          if matchingTrialDelta f M.toOrdered π c = 0 then
                            (0 : ℝ) else 1) /
                          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ) := by
                          apply div_le_div_of_nonneg_right ?_ (le_of_lt hCpos)
                          apply Finset.sum_le_sum
                          intro c _hc
                          nlinarith
                            [matchingTrialDelta_sq_le_four_rejectIndicator
                              f M.toOrdered π c]

end DictatorshipTesting
