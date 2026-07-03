import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Definition 5.22
Title in paper: Matching idempotents.

Status: re-exports the low- and high-degree matching convolution operators
currently used by the local projection/convolution helper.
-/

noncomputable section

namespace DictatorshipTesting

/-- Low-degree matching convolution operator. -/
abbrev S05_matchingLowIdempotent {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) : Perm α -> ℝ :=
  matchingLowConvolution M F

/-- High-degree matching convolution operator. -/
abbrev S05_matchingHighIdempotent {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) : Perm α -> ℝ :=
  matchingHighConvolution M F

end DictatorshipTesting
