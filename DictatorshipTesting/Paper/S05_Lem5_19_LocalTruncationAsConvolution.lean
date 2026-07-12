import DictatorshipTesting.Paper.S05_Int_PMConvolution
import DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents
import DictatorshipTesting.Paper.Defs.S04_Def4_02a_MatchingLocalProjection

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_20_CentralAveragedRejection`
-/


/-!
Paper statement: Lemma 5.19 (`lem:PM-convolution`)
Title in paper: Local truncation as convolution.

Status: proven. Paper-facing wrapper around the existing local-projection convolution
identity.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.19: local projection as low-degree convolution, with residual equal
to high-degree convolution. -/
theorem S05_Lem5_19_local_truncation_as_convolution
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    matchingLocalProjection M F = matchingLowConvolution M F ∧
      (fun π => F π - matchingLocalProjection M F π) =
        matchingHighConvolution M F := by
  exact S05_Int_PMConvolution M F

/-- Lemma 5.19 low-idempotent form: local truncation is the low matching
idempotent. -/
theorem S05_Lem5_19_local_truncation_eq_low_idempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    matchingLocalProjection M F = S05_matchingLowIdempotent M F := by
  exact (S05_Lem5_19_local_truncation_as_convolution M F).1

/-- Lemma 5.19 high-idempotent form: the residual `I - P_M` is the high
matching idempotent. -/
theorem S05_Lem5_19_residual_eq_high_idempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    (fun π => F π - matchingLocalProjection M F π) =
      S05_matchingHighIdempotent M F := by
  exact (S05_Lem5_19_local_truncation_as_convolution M F).2

end DictatorshipTesting
