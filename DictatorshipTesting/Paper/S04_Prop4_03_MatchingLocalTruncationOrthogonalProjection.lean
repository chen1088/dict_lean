import DictatorshipTesting.Paper.S04_Int_LocalHighDegreeErrorFormula
import DictatorshipTesting.Paper.S04_Int_PMFixesLocal
import DictatorshipTesting.Paper.S04_Int_PMPerpendicular

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Cor4_05_U1Local`
- `DictatorshipTesting.Paper.S04_Prop4_08_SquareEnergyControlsGlobalDegree`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
-/

/-!
# Proposition 4.3: Matching-local truncation is an orthogonal projection

This is `prop:PM-orthogonal-projection` in the STOC 2027 paper.  Its three
parts collect the fixed-space, error-formula, and perpendicularity results.
-/

namespace DictatorshipTesting

/-- Proposition 4.3(a): `P_M` maps into, and fixes, the local degree-one space. -/
theorem S04_Prop4_03_fixedSpace {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    IsMatchingLocalDegreeOne (matchingLocalProjection M F) M ∧
      ∀ H : Perm α → ℝ,
        IsMatchingLocalDegreeOne H M → matchingLocalProjection M H = H :=
  matchingLocalProjection_fixedSpace F M

/-- Proposition 4.3(b): the projection error is the local high-degree energy. -/
theorem S04_Prop4_03_errorFormula {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M = matchingLocalHighDegreeEnergy F M :=
  matchingLocalProjection_error_formula F M

/-- Proposition 4.3(c): the residual is perpendicular to the fixed space. -/
theorem S04_Prop4_03_perpendicular {α : Type*} [Fintype α] [DecidableEq α]
    (F H : Perm α → ℝ) (M : OrderedMatching α)
    (hH : IsMatchingLocalDegreeOne H M) :
    permInner (fun π => F π - matchingLocalProjection M F π) H = 0 ∧
      permInner F (fun π => F π - matchingLocalProjection M F π) =
        matchingLocalProjectionError F M :=
  matchingLocalProjection_perpendicular F H M hH

/-- Proposition 4.3, `prop:PM-orthogonal-projection`, in its combined form. -/
theorem S04_Prop4_03_MatchingLocalTruncationOrthogonalProjection
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    (IsMatchingLocalDegreeOne (matchingLocalProjection M F) M ∧
      ∀ H : Perm α → ℝ,
        IsMatchingLocalDegreeOne H M → matchingLocalProjection M H = H) ∧
    matchingLocalProjectionError F M = matchingLocalHighDegreeEnergy F M ∧
    (∀ H : Perm α → ℝ,
      IsMatchingLocalDegreeOne H M →
        permInner (fun π => F π - matchingLocalProjection M F π) H = 0) ∧
    permInner F (fun π => F π - matchingLocalProjection M F π) =
      matchingLocalProjectionError F M := by
  have hfixed := S04_Prop4_03_fixedSpace F M
  refine ⟨hfixed, S04_Prop4_03_errorFormula F M, ?_, ?_⟩
  · intro H hH
    exact (S04_Prop4_03_perpendicular F H M hH).1
  · exact
      (S04_Prop4_03_perpendicular F (matchingLocalProjection M F) M hfixed.1).2

end DictatorshipTesting
