import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungOrthogonalActionData
import DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation
import DictatorshipTesting.Paper.S05_Lem5_02_TypeAAdjacentWordPresentation

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_06a_YoungBlock`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Lem5_04_JucysMurphyRecurrences`
- `DictatorshipTesting.Paper.S05_Lem5_12_DegreeOneYoungBlockIdentification`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Thm5_05_JucysMurphyContentAction`
-/

/-!
Paper statement: Theorem 5.3 (`thm:young-orthogonal-action`)
Title in paper: Young orthogonal action.

Status: proven internally.  The type-A Coxeter normal form identifies adjacent
words modulo the relations of Lemma 5.1 with permutations.  The explicit Young
adjacent operators therefore define the required symmetric-group action.
-/


noncomputable section

namespace DictatorshipTesting

/-- The faithful Young action, constructed from the complete type-A Coxeter
presentation and the adjacent Young operators of Lemma 5.1. -/
theorem S05_Thm5_03_youngOrthogonalAction
    {n : Nat} (lam : YoungDiagram (n + 1)) :
    Nonempty (YoungOrthogonalActionData lam) := by
  exact youngOrthogonalActionData_nonempty lam



theorem S05_tableauInner_add_left {n : Nat} {lam : YoungDiagram n}
    (f g h : TableauSpace lam) :
    tableauInner (fun T => f T + g T) h =
      tableauInner f h + tableauInner g h := by
  classical
  unfold tableauInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _hT
  ring

theorem S05_tableauInner_add_right {n : Nat} {lam : YoungDiagram n}
    (f g h : TableauSpace lam) :
    tableauInner f (fun T => g T + h T) =
      tableauInner f g + tableauInner f h := by
  classical
  unfold tableauInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _hT
  ring

theorem S05_tableauInner_mul_left {n : Nat} {lam : YoungDiagram n}
    (c : Real) (f g : TableauSpace lam) :
    tableauInner (fun T => c * f T) g = c * tableauInner f g := by
  classical
  unfold tableauInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _hT
  ring

theorem S05_tableauInner_mul_right {n : Nat} {lam : YoungDiagram n}
    (c : Real) (f g : TableauSpace lam) :
    tableauInner f (fun T => c * g T) = c * tableauInner f g := by
  classical
  unfold tableauInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _hT
  ring

/-- The tableau-coordinate inner product is symmetric over the reals. -/
theorem S05_tableauInner_symm {n : Nat} {lam : YoungDiagram n}
    (f g : TableauSpace lam) :
    tableauInner f g = tableauInner g f := by
  classical
  unfold tableauInner
  apply Finset.sum_congr rfl
  intro T _hT
  ring

/-- The concrete Young adjacent operator is self-adjoint for the tableau
coordinate inner product. -/
theorem S05_tableauInner_youngAdjacentOperator_selfAdjoint
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f g : TableauSpace lam) :
    tableauInner (youngAdjacentOperator a f) g =
      tableauInner f (youngAdjacentOperator a g) := by
  classical
  unfold tableauInner youngAdjacentOperator
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _hT
  apply Finset.sum_congr rfl
  intro U _hU
  rw [youngAdjacentMatrixCoeff_symmetric]
  ring

/-- Eigenvectors of a self-adjoint Young adjacent operator with distinct real
eigenvalues are orthogonal. -/
theorem S05_tableauInner_eq_zero_of_distinct_adjacent_eigenvalues
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f g : TableauSpace lam) (x y : Real)
    (hf : youngAdjacentOperator a f = x • f)
    (hg : youngAdjacentOperator a g = y • g)
    (hxy : x ≠ y) :
    tableauInner f g = 0 := by
  have hadj := S05_tableauInner_youngAdjacentOperator_selfAdjoint a f g
  rw [hf, hg] at hadj
  change tableauInner (fun T => x * f T) g =
    tableauInner f (fun T => y * g T) at hadj
  rw [S05_tableauInner_mul_left, S05_tableauInner_mul_right] at hadj
  have hmul : (x - y) * tableauInner f g = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hxy)


/-- One concrete Young adjacent operator preserves the tableau-coordinate
inner product. -/
theorem S05_youngAdjacentOperator_inner
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f g : TableauSpace lam) :
    tableauInner (youngAdjacentOperator a f) (youngAdjacentOperator a g) =
      tableauInner f g := by
  calc
    tableauInner (youngAdjacentOperator a f) (youngAdjacentOperator a g) =
        tableauInner f
          (youngAdjacentOperator a (youngAdjacentOperator a g)) :=
      S05_tableauInner_youngAdjacentOperator_selfAdjoint a f
        (youngAdjacentOperator a g)
    _ = tableauInner f g := by rw [youngAdjacentOperator_sq]

/-- The represented inverse permutation is a left inverse on tableau
coordinates. -/
theorem YoungOrthogonalActionData.rho_leftInverse
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Perm (Fin (n + 1))) (f : TableauSpace lam) :
    action.rep.rho σ.symm (action.rep.rho σ f) = f := by
  have hσ : σ.symm * σ = 1 := by
    ext x
    simp
  calc
    action.rep.rho σ.symm (action.rep.rho σ f) =
        action.rep.rho (σ.symm * σ) f :=
      (action.rep.map_mul σ.symm σ f).symm
    _ = action.rep.rho 1 f := by rw [hσ]
    _ = f := action.rep.map_one f

/-- The represented inverse permutation is a right inverse on tableau
coordinates. -/
theorem YoungOrthogonalActionData.rho_rightInverse
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Perm (Fin (n + 1))) (f : TableauSpace lam) :
    action.rep.rho σ (action.rep.rho σ.symm f) = f := by
  have hσ : σ * σ.symm = 1 := by
    ext x
    simp
  calc
    action.rep.rho σ (action.rep.rho σ.symm f) =
        action.rep.rho (σ * σ.symm) f :=
      (action.rep.map_mul σ σ.symm f).symm
    _ = action.rep.rho 1 f := by rw [hσ]
    _ = f := action.rep.map_one f

/-- Every represented permutation acts bijectively on tableau coordinates. -/
theorem YoungOrthogonalActionData.rho_bijective
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Perm (Fin (n + 1))) :
    Function.Bijective (action.rep.rho σ) :=
  ⟨Function.LeftInverse.injective (action.rho_leftInverse σ),
    Function.RightInverse.surjective (action.rho_rightInverse σ)⟩

/-- A represented permutation, packaged with its represented inverse as a
linear equivalence. -/
noncomputable def YoungOrthogonalActionData.rhoLinearEquiv
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Perm (Fin (n + 1))) :
    TableauSpace lam ≃ₗ[Real] TableauSpace lam :=
  LinearEquiv.mk (action.rep.linearMap σ) (action.rep.rho σ.symm)
    (action.rho_leftInverse σ) (action.rho_rightInverse σ)

/-- Every represented permutation preserves the tableau-coordinate inner
product. This follows from the adjacent-generator formula and Mathlib's theorem
that adjacent transpositions generate the finite symmetric group. -/
theorem YoungOrthogonalActionData.rho_inner
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Perm (Fin (n + 1))) (f g : TableauSpace lam) :
    tableauInner (action.rep.rho σ f) (action.rep.rho σ g) =
      tableauInner f g := by
  have hmem :
      σ ∈ Submonoid.closure
        (Set.range fun a : Fin n => s05_adjacentTransposition a) := by
    rw [show
      (Set.range fun a : Fin n => s05_adjacentTransposition a) =
        Set.range (fun a : Fin n => Equiv.swap a.castSucc a.succ) by rfl]
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact Submonoid.closure_induction
    (motive := fun τ _ => ∀ u v : TableauSpace lam,
      tableauInner (action.rep.rho τ u) (action.rep.rho τ v) =
        tableauInner u v)
    (fun τ hτ => by
      rcases hτ with ⟨a, rfl⟩
      intro u v
      rw [action.rho_adjacent a u, action.rho_adjacent a v]
      exact S05_youngAdjacentOperator_inner a u v)
    (by
      intro u v
      rw [action.rep.map_one u, action.rep.map_one v])
    (fun τ υ _ _ hτ hυ => by
      intro u v
      rw [action.rep.map_mul τ υ u, action.rep.map_mul τ υ v]
      calc
        tableauInner (action.rep.rho τ (action.rep.rho υ u))
            (action.rep.rho τ (action.rep.rho υ v)) =
            tableauInner (action.rep.rho υ u) (action.rep.rho υ v) :=
          hτ _ _
        _ = tableauInner u v := hυ _ _)
    hmem f g


end DictatorshipTesting
