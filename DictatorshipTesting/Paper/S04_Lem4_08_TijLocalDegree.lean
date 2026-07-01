import DictatorshipTesting.Paper.Aux_CubeOneJuntaHighDegree
import DictatorshipTesting.Paper.L3_1_DictatorToJunta

/-!
# Lemma 4.8: A basic indicator has local degree at most one

This is `lem:tij-local-degree` from `soda27authors_section5_rethought.tex`.
-/

namespace DictatorshipTesting

/-- Lemma 4.8, `lem:tij-local-degree`: basic indicators have local degree at most one. -/
theorem L4_8_TijLocalDegree {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (i j : α) :
    IsMatchingLocalDegreeOne (oneCosetReal i j) M := by
  intro π
  let f : BoolFn α := fun ρ => decide (ρ i = j)
  have hf : IsImageDictator f := by
    refine ⟨i, fun a => decide (a = j), ?_⟩
    intro ρ
    rfl
  have hjunta : IsCubeOneJunta (matchingCubeRestriction f M π) :=
    L3_1_ImageDictatorToJunta f hf M π
  have henergy :
      cubeHighDegreeEnergy
          (fun x => boolToReal (matchingCubeRestriction f M π x)) = 0 :=
    cubeHighDegreeEnergy_boolToReal_eq_zero_of_oneJunta
      (matchingCubeRestriction f M π) hjunta
  convert henergy using 2
  ext x
  simp [f, matchingCubeRestriction, oneCosetReal, boolToReal]

end DictatorshipTesting
