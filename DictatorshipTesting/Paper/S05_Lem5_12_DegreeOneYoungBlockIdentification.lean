import DictatorshipTesting.Paper.S05_Int_DegreeOneYoungBlock
import DictatorshipTesting.Paper.S05_Lem5_11_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Thm5_03_YoungOrthogonalAction

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_22_GlobalWeightedMatchingIdentity`
-/


/-!
Paper statement: Lemma 5.12 (`lem:degree-one-young-blocks`)
Title in paper: Degree-one Young-block identification.

Status: proven internally.  The theorem below identifies `U1` with the
concrete one-row plus standard matrix-coefficient blocks.  The numerical
distance identity is derived below from this equality and the concrete
orthogonal decomposition of Lemma 5.11.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.12: degree-one Young-block identification, proved through the
explicit permutation-coordinate decomposition. -/
theorem S05_Lem5_12_degreeOneYoungBlockIdentification
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam) :
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action := by
  exact U1_eq_concreteDegreeOneYoungBlockSum action


/-- The faithful Lemma 5.12 subspace equality and the concrete orthogonal Young
decomposition identify squared distance to `U_1` with the energy in all other
Young blocks. -/
theorem l2DistSqToU1_eq_sum_concreteYoungBlockEnergy
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action)
    (F : Perm (Fin (n + 1)) -> Real) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks (n + 1)).sum
        (concreteYoungBlockEnergy action content F) := by
  classical
  let isU1Shape : YoungDiagram (n + 1) -> Prop :=
    fun lam => IsOneRow lam ∨ IsStandard lam
  let component := concreteYoungBlockComponent action content F
  let u1Part : Perm (Fin (n + 1)) -> Real :=
    ∑ lam : {lam : YoungDiagram (n + 1) // isU1Shape lam}, component lam.1
  let otherPart : Perm (Fin (n + 1)) -> Real :=
    ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam}, component lam.1
  have hsplit := Fintype.sum_subtype_add_sum_subtype isU1Shape component
  have hdecomp : u1Part + otherPart = F := by
    calc
      u1Part + otherPart =
          ∑ lam : YoungDiagram (n + 1), component lam := by
        simpa [u1Part, otherPart] using hsplit
      _ = F := sum_concreteYoungBlockComponent action content F
  have hu1Concrete : u1Part ∈ concreteDegreeOneYoungBlockSum action := by
    dsimp [u1Part]
    apply Submodule.sum_mem
    intro lam _hlam
    apply youngMatrixCoefficientBlock_le_concreteDegreeOneYoungBlockSum
      action lam.1 lam.2
    exact concreteYoungBlockComponent_mem action content F lam.1
  have hu1 : u1Part ∈ U1 (Fin (n + 1)) := by
    rw [hU1]
    exact hu1Concrete
  have hother_orthogonal :
      ∀ G : Perm (Fin (n + 1)) -> Real,
        G ∈ concreteDegreeOneYoungBlockSum action ->
          permInner otherPart G = 0 := by
    intro G hG
    unfold concreteDegreeOneYoungBlockSum at hG
    refine Submodule.iSup_induction
      (fun lam : YoungDiagram (n + 1) =>
        ⨆ (_h : IsOneRow lam ∨ IsStandard lam),
          youngMatrixCoefficientBlock (action lam))
      (motive := fun G => permInner otherPart G = 0) hG ?_ ?_ ?_
    · intro lam G hGlam
      refine Submodule.iSup_induction
        (fun _h : IsOneRow lam ∨ IsStandard lam =>
          youngMatrixCoefficientBlock (action lam))
        (motive := fun G => permInner otherPart G = 0) hGlam ?_ ?_ ?_
      · intro hlam G hGblock
        calc
          permInner otherPart G =
              ∑ mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu},
                permInner (component mu.1) G := by
            simpa [otherPart] using
              permInner_fintype_sum_smul_left
                (fun _mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu} =>
                  (1 : Real))
                (fun mu => component mu.1) G
          _ = 0 := by
            apply Finset.sum_eq_zero
            intro mu _hmu
            have hshape : mu.1 ≠ lam := by
              intro heq
              apply mu.2
              dsimp [isU1Shape]
              simpa [heq] using hlam
            exact youngMatrixCoefficientBlock_orthogonal
              hshape (action mu.1) (content mu.1)
                (action lam) (content lam)
                (concreteYoungBlockComponent_mem action content F mu.1)
                hGblock
      · exact permInner_zero_right otherPart
      · intro G₁ G₂ h₁ h₂
        rw [permInner_add_right, h₁, h₂, add_zero]
    · exact permInner_zero_right otherPart
    · intro G₁ G₂ h₁ h₂
      rw [permInner_add_right, h₁, h₂, add_zero]
  have hotherNorm :
      permInner otherPart otherPart =
        (nonU1YoungBlocks (n + 1)).sum
          (concreteYoungBlockEnergy action content F) := by
    calc
      permInner otherPart otherPart =
          ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
            permInner (component lam.1) otherPart := by
        simpa [otherPart] using
          permInner_fintype_sum_smul_left
            (fun _lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam} =>
              (1 : Real))
            (fun lam => component lam.1) otherPart
      _ = ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
          ∑ mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu},
            permInner (component lam.1) (component mu.1) := by
        apply Finset.sum_congr rfl
        intro lam _hlam
        simpa [otherPart] using
          permInner_fintype_sum_smul_right
            (fun _mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu} =>
              (1 : Real))
            (fun mu => component mu.1) (component lam.1)
      _ = ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
          permInner (component lam.1) (component lam.1) := by
        apply Finset.sum_congr rfl
        intro lam _hlam
        rw [Fintype.sum_eq_single lam]
        intro mu hmulam
        apply concreteYoungBlockComponent_orthogonal action content F
        intro hshape
        apply hmulam
        exact Subtype.ext hshape.symm
      _ = ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
          concreteYoungBlockEnergy action content F lam.1 := by
        rfl
      _ = (nonU1YoungBlocks (n + 1)).sum
          (concreteYoungBlockEnergy action content F) := by
        symm
        apply Finset.sum_subtype
        intro lam
        simp [nonU1YoungBlocks, isU1Shape]
  have hpythagoras
      (G : Perm (Fin (n + 1)) -> Real) (hG : G ∈ U1 (Fin (n + 1))) :
      l2DistSq F G =
        (nonU1YoungBlocks (n + 1)).sum
            (concreteYoungBlockEnergy action content F) +
          l2DistSq u1Part G := by
    have hu1_sub_G : u1Part - G ∈ U1 (Fin (n + 1)) :=
      Submodule.sub_mem _ hu1 hG
    have hu1_sub_G_concrete :
        u1Part - G ∈ concreteDegreeOneYoungBlockSum action := by
      rw [← hU1]
      exact hu1_sub_G
    have horth : permInner otherPart (u1Part - G) = 0 :=
      hother_orthogonal (u1Part - G) hu1_sub_G_concrete
    have horth' : permInner (u1Part - G) otherPart = 0 := by
      rw [permInner_symm]
      exact horth
    have hdiff : F - G = otherPart + (u1Part - G) := by
      rw [← hdecomp]
      abel
    rw [l2DistSq_eq_permInner_sub, l2DistSq_eq_permInner_sub, hdiff]
    calc
      permInner (otherPart + (u1Part - G))
          (otherPart + (u1Part - G)) =
          permInner otherPart otherPart +
            permInner otherPart (u1Part - G) +
            permInner (u1Part - G) otherPart +
            permInner (u1Part - G) (u1Part - G) := by
        rw [permInner_add_left, permInner_add_right, permInner_add_right]
        ring
      _ = permInner otherPart otherPart +
          permInner (u1Part - G) (u1Part - G) := by
        rw [horth, horth']
        ring
      _ = (nonU1YoungBlocks (n + 1)).sum
            (concreteYoungBlockEnergy action content F) +
          permInner (u1Part - G) (u1Part - G) := by
        rw [hotherNorm]
  let distances : Set Real :=
    {d : Real | ∃ G : Perm (Fin (n + 1)) -> Real,
      G ∈ U1 (Fin (n + 1)) ∧ d = l2DistSq F G}
  let otherEnergy : Real :=
    (nonU1YoungBlocks (n + 1)).sum
      (concreteYoungBlockEnergy action content F)
  have hotherEnergy_mem : otherEnergy ∈ distances := by
    refine ⟨u1Part, hu1, ?_⟩
    have h := hpythagoras u1Part hu1
    simpa [otherEnergy, l2DistSq] using h.symm
  have hdistances_nonempty : distances.Nonempty :=
    ⟨otherEnergy, hotherEnergy_mem⟩
  have hdistances_bddBelow : BddBelow distances := by
    refine ⟨0, ?_⟩
    intro d hd
    rcases hd with ⟨G, _hG, rfl⟩
    unfold l2DistSq
    positivity
  have hotherEnergy_lower : ∀ d ∈ distances, otherEnergy ≤ d := by
    intro d hd
    rcases hd with ⟨G, hG, rfl⟩
    rw [hpythagoras G hG]
    dsimp [otherEnergy]
    apply le_add_of_nonneg_right
    unfold l2DistSq
    positivity
  unfold l2DistSqToU1
  change sInf distances = otherEnergy
  exact le_antisymm
    (csInf_le hdistances_bddBelow hotherEnergy_mem)
    (le_csInf hdistances_nonempty hotherEnergy_lower)

/-- Lemma Lemma 5.12 numerical consequence for the concrete Young-block energies. -/
theorem S05_Lem5_12_l2DistSqToU1_eq_nonU1_sum
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) -> Real) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks (n + 1)).sum
        (concreteYoungBlockEnergy action content F) := by
  exact l2DistSqToU1_eq_sum_concreteYoungBlockEnergy action content
    (S05_Lem5_12_degreeOneYoungBlockIdentification action) F


end DictatorshipTesting
