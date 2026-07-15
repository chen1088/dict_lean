import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingTrialDelta
import DictatorshipTesting.Paper.S03_Lem3_01_DictatorToJunta

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Lem4_07_IndependentRepetition`
-/
/-!
# Lemma 3.2: Perfect completeness

This is the cube-level cancellation used in `lem:perfect-completeness` from
`dictatorship_testing_stoc27_shortened.tex`.
-/

namespace DictatorshipTesting

/-- A one-junta has zero mixed second
difference along the disjoint directions sampled by one matching-cube trial. -/
theorem cubeOneJunta_square_zero {m : ℕ} (g : FinCube m → Bool)
    (hg : IsCubeOneJunta g) {x u v : FinCube m}
    (hdisj : CubeDirectionsDisjoint u v) :
    cubeDelta (fun y => boolToReal (g y)) x u v = 0 := by
  rcases hg with hconst | hjunta
  · have hx1 : g (cubeXor x u) = g x := hconst _ _
    have hx2 : g (cubeXor x v) = g x := hconst _ _
    have hx3 : g (cubeXor (cubeXor x u) v) = g x := hconst _ _
    simp [cubeDelta, hx1, hx2, hx3]
  · rcases hjunta with ⟨r, hr⟩
    cases hu : u r <;> cases hv : v r
    · have hx1 : g (cubeXor x u) = g x := by
        apply hr
        simp [cubeXor, hu]
      have hx2 : g (cubeXor x v) = g x := by
        apply hr
        simp [cubeXor, hv]
      have hx3 : g (cubeXor (cubeXor x u) v) = g x := by
        apply hr
        simp [cubeXor, hu, hv]
      simp [cubeDelta, hx1, hx2, hx3]
    · have hx1 : g (cubeXor x u) = g x := by
        apply hr
        simp [cubeXor, hu]
      have hx3 : g (cubeXor (cubeXor x u) v) = g (cubeXor x v) := by
        apply hr
        simp [cubeXor, hu]
      simp [cubeDelta, hx1, hx3]
    · have hx2 : g (cubeXor x v) = g x := by
        apply hr
        simp [cubeXor, hv]
      have hx3 : g (cubeXor (cubeXor x u) v) = g (cubeXor x u) := by
        apply hr
        simp [cubeXor, hv]
      simp [cubeDelta, hx2, hx3]
    · have hvfalse : v r = false := hdisj r hu
      simp [hv] at hvfalse

/-- The color encoding used by the test always produces disjoint directions. -/
theorem cubeColor_directionsDisjoint {m : ℕ} (c : CubeDirectionColor m) :
    CubeDirectionsDisjoint (cubeColorU c) (cubeColorV c) := by
  intro r hur
  apply decide_eq_false
  intro hv
  have hu : c r = (1 : Fin 3) := of_decide_eq_true hur
  have h12 : (1 : Fin 3) = 2 := hu.symm.trans hv
  have hval := congrArg Fin.val h12
  norm_num at hval

/-- Lemma 3.2, `lem:perfect-completeness`: dictators are accepted by one
matching-cube square trial. -/
theorem S03_Lem3_02_PerfectCompleteness {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsDictator f)
    (M : OrderedMatching α) (π : Perm α) (c : CubeDirectionColor M.edgeCount) :
    matchingTrialDelta f M π c = 0 := by
  unfold matchingTrialDelta
  exact cubeOneJunta_square_zero (matchingCubeRestriction f M π)
    (S03_Lem3_01_DictatorToJunta f hf M π)
    (x := finCubeZero M.edgeCount)
    (u := cubeColorU c) (v := cubeColorV c)
    (cubeColor_directionsDisjoint c)

end DictatorshipTesting
