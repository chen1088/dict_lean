import DictatorshipTesting.Paper.S05_Def5_17_MatchingCharacters

/-!
Paper statement: Definition 5.21 (`def:matching-idempotents`)
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

/-- Low-character index set for the matching cube. -/
def S05_matchingLowCharacterSet {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) : Finset (Finset (Fin M.edgeCount)) :=
  Finset.univ.filter (fun S : Finset (Fin M.edgeCount) =>
    S05_matchingCharacterLow S)

/-- High-character index set for the matching cube. -/
def S05_matchingHighCharacterSet {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) : Finset (Finset (Fin M.edgeCount)) :=
  Finset.univ.filter (fun S : Finset (Fin M.edgeCount) =>
    S05_matchingCharacterHigh S)

/-- Membership in the low-character index set. -/
theorem S05_mem_matchingLowCharacterSet_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (S : Finset (Fin M.edgeCount)) :
    S ∈ S05_matchingLowCharacterSet M ↔ S05_matchingCharacterLow S := by
  simp [S05_matchingLowCharacterSet]

/-- Membership in the high-character index set. -/
theorem S05_mem_matchingHighCharacterSet_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (S : Finset (Fin M.edgeCount)) :
    S ∈ S05_matchingHighCharacterSet M ↔ S05_matchingCharacterHigh S := by
  simp [S05_matchingHighCharacterSet]

/-- The low matching idempotent is the low-character Fourier sum on the
matching cube. -/
theorem S05_matchingLowIdempotent_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) (π : Perm α) :
    S05_matchingLowIdempotent M F π =
      ∑ S ∈ S05_matchingLowCharacterSet M,
        cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
          S05_matchingCharacter S (cubeZero M.edgeCount) := by
  rfl

/-- The high matching idempotent is the high-character Fourier sum on the
matching cube. -/
theorem S05_matchingHighIdempotent_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) (π : Perm α) :
    S05_matchingHighIdempotent M F π =
      ∑ S ∈ S05_matchingHighCharacterSet M,
        cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
          S05_matchingCharacter S (cubeZero M.edgeCount) := by
  rfl

end DictatorshipTesting
