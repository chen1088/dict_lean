import DictatorshipTesting.Paper.Defs.S05_Def5_05_ContentAndAdjacentOperators

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_JucysMurphyContentActionData`
- `DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation`
- `DictatorshipTesting.Paper.S05_Int_ConcreteYoungMatrixCoefficientBlocks`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Thm5_03_YoungOrthogonalAction`
-/

/-!
Section 5 interface definition for Theorem Theorem 5.3.

This structure records only the Young orthogonal representation action and its
identification with the explicit adjacent tableau operators.  It contains no
block energies, trace values, or scalarity fields.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A real finite group-algebra element, represented by its coefficient
function. -/
abbrev GroupAlgebraElement (G : Type*) [Fintype G] :=
  G -> Real

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

/-- The literal adjacent transposition `(a,a+1)` in `S_(n+1)`. -/
def s05_adjacentTransposition {n : Nat} (a : Fin n) :
    Perm (Fin (n + 1)) :=
  Equiv.swap a.castSucc a.succ

/-- Faithful Lean data for Section 5.1: a representation of the symmetric
group on one tableau-coordinate Young space whose adjacent generators are the
explicit Young adjacent operators. -/
structure YoungOrthogonalActionData {n : Nat}
    (lam : YoungDiagram (n + 1)) where
  rep :
    GroupRepresentationActionData (Perm (Fin (n + 1))) (TableauSpace lam)
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


end DictatorshipTesting
