import DictatorshipTesting.Paper.Defs.S03_Def3_23_MatchingMeanProjectionError
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_25_OneTrialRejectProbability`
-/


/-!
Definition file for `oneTrialDeltaSqExpectation`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Mean square of the alternating sum queried by one matching-cube trial. -/
def oneTrialDeltaSqExpectation {n : ℕ}
    (F : Perm (Fin n) → ℝ) : ℝ :=
  (∑ M : NearPerfectMatching n,
    (∑ π : Perm (Fin n),
      (∑ c : CubeDirectionColor (n / 2),
        (matchingTrialDeltaReal F M.toOrdered π c) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
        (Fintype.card (Perm (Fin n)) : ℝ)) /
      (Fintype.card (NearPerfectMatching n) : ℝ)

end DictatorshipTesting
