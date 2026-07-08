import DictatorshipTesting.Paper.Aux_MatchingLocalProjection
import DictatorshipTesting.Paper.Aux_PMConvolution
import DictatorshipTesting.Paper.S05_Def5_22_MatchingCharacters

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper.S05_Lem5_27_LocalTruncationAsConvolution`
- `DictatorshipTesting.PaperAux`
- `DictatorshipTesting.PaperPlaceholders`
-/

/-!
Paper statement: Definition 5.26 (`def:matching-idempotents`)
Title in paper: Matching idempotents.

Status: definition/interface. Re-exports the low- and high-degree matching convolution operators
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

/-- The matching-local projection is idempotent. -/
theorem matchingLocalProjection_idempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    matchingLocalProjection M (matchingLocalProjection M F) =
      matchingLocalProjection M F := by
  funext π
  let g : Cube M.edgeCount -> ℝ := fun x => F (π * M.tau x)
  have hrestrict :
      (fun y : Cube M.edgeCount =>
        matchingLocalProjection M F (π * M.tau y)) =
        cubeLowDegreeOnePart g := by
    funext y
    exact matchingLocalProjection_apply_mul_tau M F π y
  calc
    matchingLocalProjection M (matchingLocalProjection M F) π =
        cubeLowDegreeOnePart
          (fun y : Cube M.edgeCount =>
            matchingLocalProjection M F (π * M.tau y))
          (cubeZero M.edgeCount) := rfl
    _ = cubeLowDegreeOnePart (cubeLowDegreeOnePart g)
          (cubeZero M.edgeCount) := by
        rw [hrestrict]
    _ = cubeLowDegreeOnePart g (cubeZero M.edgeCount) := by
        rw [cubeLowDegreeOnePart_idempotent g]
    _ = matchingLocalProjection M F π := rfl

/-- The high matching convolution is killed by the matching-local projection. -/
theorem matchingLocalProjection_highConvolution_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    matchingLocalProjection M (matchingHighConvolution M F) = fun _ => 0 := by
  funext π
  let g : Cube M.edgeCount -> ℝ := fun x => F (π * M.tau x)
  calc
    matchingLocalProjection M (matchingHighConvolution M F) π =
        matchingLocalProjection M
          (fun ρ => F ρ - matchingLocalProjection M F ρ) π := by
        rw [(L5_1_PMConvolution M F).2]
    _ =
        cubeLowDegreeOnePart
          (fun y : Cube M.edgeCount =>
            (fun ρ => F ρ - matchingLocalProjection M F ρ)
              (π * M.tau y))
          (cubeZero M.edgeCount) := rfl
    _ =
        cubeLowDegreeOnePart
          (fun y : Cube M.edgeCount => g y - cubeLowDegreeOnePart g y)
          (cubeZero M.edgeCount) := by
        congr
        funext y
        dsimp [g]
        rw [matchingLocalProjection_apply_mul_tau M F π y]
    _ = 0 := by
        rw [cubeLowDegreeOnePart_lowDegreeResidual_eq_zero g]

/-- The low matching idempotent is genuinely idempotent. -/
theorem S05_matchingLowIdempotent_idempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    S05_matchingLowIdempotent M (S05_matchingLowIdempotent M F) =
      S05_matchingLowIdempotent M F := by
  calc
    S05_matchingLowIdempotent M (S05_matchingLowIdempotent M F) =
        matchingLocalProjection M (S05_matchingLowIdempotent M F) := by
        change
          matchingLowConvolution M (S05_matchingLowIdempotent M F) =
            matchingLocalProjection M (S05_matchingLowIdempotent M F)
        exact ((L5_1_PMConvolution M
          (S05_matchingLowIdempotent M F)).1).symm
    _ = matchingLocalProjection M (matchingLocalProjection M F) := by
        exact congrArg (fun G => matchingLocalProjection M G)
          (by
            change matchingLowConvolution M F = matchingLocalProjection M F
            exact ((L5_1_PMConvolution M F).1).symm)
    _ = matchingLocalProjection M F := by
        rw [matchingLocalProjection_idempotent M F]
    _ = S05_matchingLowIdempotent M F := by
        exact (L5_1_PMConvolution M F).1

/-- The high matching idempotent is genuinely idempotent. -/
theorem S05_matchingHighIdempotent_idempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    S05_matchingHighIdempotent M (S05_matchingHighIdempotent M F) =
      S05_matchingHighIdempotent M F := by
  change
    matchingHighConvolution M (S05_matchingHighIdempotent M F) =
      S05_matchingHighIdempotent M F
  rw [← (L5_1_PMConvolution M (S05_matchingHighIdempotent M F)).2]
  change
    (fun π => S05_matchingHighIdempotent M F π -
      matchingLocalProjection M (matchingHighConvolution M F) π) =
      S05_matchingHighIdempotent M F
  rw [matchingLocalProjection_highConvolution_eq_zero M F]
  funext π
  simp

/-- The low matching idempotent kills the high matching idempotent. -/
theorem S05_matchingLowIdempotent_high_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    S05_matchingLowIdempotent M (S05_matchingHighIdempotent M F) =
      fun _ => 0 := by
  calc
    S05_matchingLowIdempotent M (S05_matchingHighIdempotent M F) =
        matchingLocalProjection M (S05_matchingHighIdempotent M F) := by
        change
          matchingLowConvolution M (S05_matchingHighIdempotent M F) =
            matchingLocalProjection M (S05_matchingHighIdempotent M F)
        exact ((L5_1_PMConvolution M
          (S05_matchingHighIdempotent M F)).1).symm
    _ = fun _ => 0 := by
        change matchingLocalProjection M (matchingHighConvolution M F) = fun _ => 0
        exact matchingLocalProjection_highConvolution_eq_zero M F

/-- The high matching idempotent kills the low matching idempotent. -/
theorem S05_matchingHighIdempotent_low_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    S05_matchingHighIdempotent M (S05_matchingLowIdempotent M F) =
      fun _ => 0 := by
  have hproj :
      matchingLocalProjection M (S05_matchingLowIdempotent M F) =
        S05_matchingLowIdempotent M F := by
    calc
      matchingLocalProjection M (S05_matchingLowIdempotent M F) =
          S05_matchingLowIdempotent M (S05_matchingLowIdempotent M F) := by
          exact (L5_1_PMConvolution M (S05_matchingLowIdempotent M F)).1
      _ = S05_matchingLowIdempotent M F := by
          exact S05_matchingLowIdempotent_idempotent M F
  change
    matchingHighConvolution M (S05_matchingLowIdempotent M F) =
      fun _ => 0
  rw [← (L5_1_PMConvolution M (S05_matchingLowIdempotent M F)).2]
  funext π
  rw [hproj]
  simp

/-- The low and high matching idempotents decompose the identity. -/
theorem S05_matchingLow_add_matchingHigh
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> ℝ) :
    (fun π => S05_matchingLowIdempotent M F π +
      S05_matchingHighIdempotent M F π) = F := by
  have hlow := (L5_1_PMConvolution M F).1
  have hhigh := (L5_1_PMConvolution M F).2
  funext π
  change matchingLowConvolution M F π + matchingHighConvolution M F π = F π
  rw [← hlow, ← hhigh]
  ring

end DictatorshipTesting
