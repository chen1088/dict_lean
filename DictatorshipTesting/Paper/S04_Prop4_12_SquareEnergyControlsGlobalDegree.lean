import DictatorshipTesting.Paper.Aux_OneTrialDeltaSqExpectationLowerBound
import DictatorshipTesting.Paper.S04_Thm4_10_MatchingGap

/-!
# Proposition 4.12: Square energy controls global degree

This is the proposition containing equation `eq:square-energy-global-bound`.
-/

namespace DictatorshipTesting

/-- Proposition 4.12: square energy controls global degree. -/
theorem Prop4_12_SquareEnergyControlsGlobalDegree
    (n : ℕ) (hn : 4 ≤ n)
    (F : Perm (Fin n) → ℝ) :
    (16 / 27 : ℝ) * l2DistSqToU1 F ≤ oneTrialDeltaSqExpectation F := by
  have hgap :
      (1 / 6 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F :=
    (Thm4_10_MatchingGap n hn F).1
  have htrial :
      (32 / 9 : ℝ) * matchingMeanProjectionError F ≤
        oneTrialDeltaSqExpectation F :=
    oneTrialDeltaSqExpectation_ge_matchingMeanProjectionError n F
  calc
    (16 / 27 : ℝ) * l2DistSqToU1 F =
        (32 / 9 : ℝ) * ((1 / 6 : ℝ) * l2DistSqToU1 F) := by
          ring
    _ ≤ (32 / 9 : ℝ) * matchingMeanProjectionError F := by
          nlinarith
    _ ≤ oneTrialDeltaSqExpectation F := htrial

end DictatorshipTesting
