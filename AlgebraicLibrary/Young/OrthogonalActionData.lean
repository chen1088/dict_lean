import AlgebraicLibrary.Young.OrthogonalRepresentation
import AlgebraicLibrary.Algebra.OperatorProduct

/-!
Section 5 interface definition for Theorem Theorem 5.3.

This structure records only the Young orthogonal representation action and its
identification with the explicit adjacent tableau operators.  It contains no
block energies, trace values, or scalarity fields.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- A real finite group-algebra element, represented by its coefficient
function. -/
abbrev GroupAlgebraElement (G : Type*) [Fintype G] :=
  G -> Real

namespace GroupAlgebraElement

/-- Coefficient-level commutation with a group element. -/
def CommutesWithGroupElement {G : Type*} [Fintype G] [Group G]
    (a : GroupAlgebraElement G) (s : G) : Prop :=
  ∀ g : G, a (g * s⁻¹) = a (s⁻¹ * g)

/-- Coefficient-level centrality against every group element. -/
def IsCentralByCoefficients {G : Type*} [Fintype G] [Group G]
    (a : GroupAlgebraElement G) : Prop :=
  ∀ s : G, a.CommutesWithGroupElement s

end GroupAlgebraElement

/-- A finite group representation on a real module, in the pointwise form
needed by the group-algebra action. -/
structure GroupRepresentationActionData
    (G V : Type*) [Group G] [AddCommMonoid V] [Module Real V] where
  rho : G -> V -> V
  map_add :
    forall g : G, forall v w : V, rho g (v + w) = rho g v + rho g w
  map_smul :
    forall g : G, forall (c : Real) (v : V), rho g (c • v) = c • rho g v
  map_mul :
    forall g h : G, forall v : V, rho (g * h) v = rho g (rho h v)
  map_one :
    forall v : V, rho 1 v = v

/-- One represented group element, packaged as a linear map. -/
def GroupRepresentationActionData.linearMap
    {G V : Type*} [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V) (g : G) : V →ₗ[Real] V where
  toFun := rep.rho g
  map_add' := rep.map_add g
  map_smul' := rep.map_smul g

/-- A represented list product acts by composing the represented factors in
the displayed order. -/
theorem GroupRepresentationActionData.rho_list_prod
    {G V : Type*} [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V) (l : List G) (v : V) :
    rep.rho l.prod v = composeOperatorList (l.map rep.rho) v := by
  induction l with
  | nil =>
      simp [composeOperatorList, rep.map_one]
  | cons g l ih =>
      simp only [List.prod_cons, List.map_cons, composeOperatorList]
      rw [rep.map_mul, ih]

/-- The literal adjacent transposition `(a,a+1)` in `S_(n+1)`. -/
def s05_adjacentTransposition {n : Nat} (a : Fin n) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap a.castSucc a.succ

/-- Faithful Lean data for Section 5.1: a representation of the symmetric
group on one tableau-coordinate Young space whose adjacent generators are the
explicit Young adjacent operators. -/
structure YoungOrthogonalActionData {n : Nat}
    (lam : YoungDiagram (n + 1)) where
  rep :
    GroupRepresentationActionData (Equiv.Perm (Fin (n + 1))) (TableauSpace lam)
  rho_adjacent :
    forall a : Fin n, forall f : TableauSpace lam,
      rep.rho (s05_adjacentTransposition a) f = youngAdjacentOperator a f


/-- The operator `rho(a) = sum_g a(g) rho(g)` attached to a finite
group-algebra element. -/
def repOfGroupAlgebraElement {G V : Type*} [Fintype G] [Group G]
    [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : GroupAlgebraElement G) : V -> V :=
  fun v => ∑ g : G, a g • rep.rho g v

/-- The group-algebra action is additive in the vector. -/
theorem repOfGroupAlgebraElement_map_add {G V : Type*}
    [Fintype G] [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : GroupAlgebraElement G) (v w : V) :
    repOfGroupAlgebraElement rep a (v + w) =
      repOfGroupAlgebraElement rep a v +
        repOfGroupAlgebraElement rep a w := by
  simp [repOfGroupAlgebraElement, rep.map_add, smul_add,
    Finset.sum_add_distrib]

/-- The group-algebra action is homogeneous in the vector. -/
theorem repOfGroupAlgebraElement_map_smul {G V : Type*}
    [Fintype G] [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : GroupAlgebraElement G) (c : Real) (v : V) :
    repOfGroupAlgebraElement rep a (c • v) =
      c • repOfGroupAlgebraElement rep a v := by
  rw [repOfGroupAlgebraElement, repOfGroupAlgebraElement]
  calc
    (∑ g : G, a g • rep.rho g (c • v))
        = ∑ g : G, a g • (c • rep.rho g v) := by
            simp [rep.map_smul]
    _ = ∑ g : G, c • (a g • rep.rho g v) := by
            apply Finset.sum_congr rfl
            intro g hg
            simp [smul_smul, mul_comm]
    _ = c • ∑ g : G, a g • rep.rho g v := by
            rw [Finset.smul_sum]

/-- The represented group-algebra element, packaged as a linear map. -/
def repOfGroupAlgebraElementLinearMap {G V : Type*}
    [Fintype G] [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : GroupAlgebraElement G) : V →ₗ[Real] V where
  toFun := repOfGroupAlgebraElement rep a
  map_add' := repOfGroupAlgebraElement_map_add rep a
  map_smul' := repOfGroupAlgebraElement_map_smul rep a

/-- Representing a coefficientwise finite average gives the corresponding
finite average of the represented operators. -/
theorem repOfGroupAlgebraElement_fintypeAverage
    {G V ι : Type*} [Fintype G] [Group G]
    [Fintype ι] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : ι -> GroupAlgebraElement G) (v : V) :
    repOfGroupAlgebraElement rep
        (fun g => (∑ i : ι, a i g) / (Fintype.card ι : Real)) v =
      (Fintype.card ι : Real)⁻¹ •
        ∑ i : ι, repOfGroupAlgebraElement rep (a i) v := by
  classical
  unfold repOfGroupAlgebraElement
  calc
    (∑ g : G,
      ((∑ i : ι, a i g) / (Fintype.card ι : Real)) • rep.rho g v) =
        ∑ g : G, ∑ i : ι,
          (Fintype.card ι : Real)⁻¹ • (a i g • rep.rho g v) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [← Finset.smul_sum, ← Finset.sum_smul]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
    _ = ∑ i : ι, ∑ g : G,
          (Fintype.card ι : Real)⁻¹ • (a i g • rep.rho g v) := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι, (Fintype.card ι : Real)⁻¹ •
          ∑ g : G, a i g • rep.rho g v := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.smul_sum]
    _ = (Fintype.card ι : Real)⁻¹ •
        ∑ i : ι, ∑ g : G, a i g • rep.rho g v := by
      rw [Finset.smul_sum]

namespace YoungOrthogonalActionData

/-- The represented inverse permutation is a left inverse. -/
theorem rho_leftInverse {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Equiv.Perm (Fin (n + 1))) (f : TableauSpace lam) :
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

/-- The represented inverse permutation is a right inverse. -/
theorem rho_rightInverse {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Equiv.Perm (Fin (n + 1))) (f : TableauSpace lam) :
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

/-- Every represented permutation acts bijectively. -/
theorem rho_bijective {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Equiv.Perm (Fin (n + 1))) :
    Function.Bijective (action.rep.rho σ) :=
  ⟨Function.LeftInverse.injective (action.rho_leftInverse σ),
    Function.RightInverse.surjective (action.rho_rightInverse σ)⟩

/-- A represented permutation packaged with its inverse as a linear
equivalence. -/
noncomputable def rhoLinearEquiv {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Equiv.Perm (Fin (n + 1))) :
    TableauSpace lam ≃ₗ[ℝ] TableauSpace lam :=
  LinearEquiv.mk (action.rep.linearMap σ) (action.rep.rho σ.symm)
    (action.rho_leftInverse σ) (action.rho_rightInverse σ)

/-- Every represented permutation preserves the tableau-coordinate inner
product. -/
theorem rho_inner {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (σ : Equiv.Perm (Fin (n + 1))) (f g : TableauSpace lam) :
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
      exact youngAdjacentOperator_inner a u v)
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

end YoungOrthogonalActionData


end AlgebraicLibrary
