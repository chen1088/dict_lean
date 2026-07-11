import DictatorshipTesting.Paper.Defs.S05_Def5_05_ContentAndAdjacentOperators

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_JucysMurphyContentActionData`
- `DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation`
- `DictatorshipTesting.Paper.S05_Int_ConcreteYoungMatrixCoefficientBlocks`
- `DictatorshipTesting.Paper.S05_Lem5_20_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Thm5_03_YoungOrthogonalAction`
-/

/-!
Section 5 interface definition for Theorem Theorem 5.3.

This structure records only the Young orthogonal representation action and its
identification with the explicit adjacent tableau operators.  It contains no
block energies, trace values, or scalarity fields.
-/

noncomputable section

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

end DictatorshipTesting
