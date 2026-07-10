import DictatorshipTesting.Paper.S05_Lem5_16a_AveragedRejectionYoungOperator

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_29_AveragedHighMatchingElement`
-/

/-!
Paper statement: Definition 5.28 (`def:group-algebra-action-interface`)
Title in paper: Group-algebra action interface.

Status: definition/interface.  This file adds the finite group-algebra and
representation-action vocabulary needed to state the remaining averaged
matching-rejection instantiation problem.  It does not assert scalarity and does
not replace the named Section 5 scalarity input.
-/

noncomputable section

namespace DictatorshipTesting

/-- A real finite group-algebra element, represented as its coefficient
function.  For the active Section 5 route the intended group is a finite
symmetric group. -/
abbrev GroupAlgebraElement (G : Type*) [Fintype G] :=
  G -> Real

/-- Right convolution by a finite group-algebra element:
`(C_a F)(x) = sum_g a(g) F(xg)`. -/
def rightConvolution {G : Type*} [Fintype G] [Mul G]
    (a : GroupAlgebraElement G) (F : G -> Real) : G -> Real :=
  fun x => ∑ g : G, a g * F (x * g)

/-- Right convolution is additive in the function being convolved. -/
theorem rightConvolution_add {G : Type*} [Fintype G] [Mul G]
    (a : GroupAlgebraElement G) (F H : G -> Real) :
    rightConvolution a (fun x => F x + H x) =
      fun x => rightConvolution a F x + rightConvolution a H x := by
  funext x
  simp [rightConvolution, mul_add, Finset.sum_add_distrib]

/-- Right convolution is homogeneous in the function being convolved. -/
theorem rightConvolution_smul {G : Type*} [Fintype G] [Mul G]
    (a : GroupAlgebraElement G) (c : Real) (F : G -> Real) :
    rightConvolution a (fun x => c * F x) =
      fun x => c * rightConvolution a F x := by
  funext x
  simp [rightConvolution, Finset.mul_sum, mul_left_comm]

/-- A representation-like finite group action on a real module, stated only in
the form needed to sum group elements with group-algebra coefficients. -/
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

/-- Coefficient-level commutation with a group element.  This is the narrow
centrality condition needed for changing variables in `rho(a) rho(s)` versus
`rho(s) rho(a)`. -/
def GroupAlgebraElement.CommutesWithGroupElement {G : Type*}
    [Fintype G] [Group G] (a : GroupAlgebraElement G) (s : G) : Prop :=
  forall g : G, a (g * s⁻¹) = a (s⁻¹ * g)

/-- Coefficient-level centrality against every group element. -/
def GroupAlgebraElement.IsCentralByCoefficients {G : Type*}
    [Fintype G] [Group G] (a : GroupAlgebraElement G) : Prop :=
  forall s : G, a.CommutesWithGroupElement s

/-- The statement that `rho(a)` commutes with every represented group
element.  This is a representation-action obligation, not scalarity. -/
def RepElementCommutesWithGroupAction {G V : Type*}
    [Fintype G] [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : GroupAlgebraElement G) : Prop :=
  forall s : G, forall v : V,
    repOfGroupAlgebraElement rep a (rep.rho s v) =
      rep.rho s (repOfGroupAlgebraElement rep a v)

/-- Coefficient-level centrality implies that the represented group-algebra
element commutes with every represented group element.  The proof is the
finite change of variables `g \mapsto s g s^{-1}`. -/
theorem repOfGroupAlgebraElement_commutes_of_central
    {G V : Type*} [Fintype G] [Group G]
    [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a : GroupAlgebraElement G)
    (hcentral : a.IsCentralByCoefficients) :
    RepElementCommutesWithGroupAction rep a := by
  classical
  intro s v
  let conj : G ≃ G := (Equiv.mulLeft s).trans (Equiv.mulRight s⁻¹)
  have hcoeff (g : G) : a (s * g * s⁻¹) = a g := by
    have h := hcentral s (s * g)
    simpa [GroupAlgebraElement.CommutesWithGroupElement, mul_assoc] using h
  unfold repOfGroupAlgebraElement
  calc
    (∑ g : G, a g • rep.rho g (rep.rho s v)) =
        ∑ g : G, a g • rep.rho (g * s) v := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [rep.map_mul]
    _ = ∑ g : G,
        a (s * g * s⁻¹) • rep.rho ((s * g * s⁻¹) * s) v := by
      exact (Equiv.sum_comp conj
        (fun g : G => a g • rep.rho (g * s) v)).symm
    _ = ∑ g : G, a g • rep.rho (s * g) v := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [hcoeff]
      simp [mul_assoc]
    _ = ∑ g : G, rep.linearMap s (a g • rep.rho g v) := by
      apply Finset.sum_congr rfl
      intro g _hg
      change a g • rep.rho (s * g) v = rep.rho s (a g • rep.rho g v)
      rw [rep.map_mul, rep.map_smul]
    _ = rep.linearMap s (∑ g : G, a g • rep.rho g v) := by
      rw [map_sum]
    _ = rep.rho s (∑ g : G, a g • rep.rho g v) := rfl

/-- The statement that two represented group-algebra elements commute. -/
def RepElementsCommute {G V : Type*}
    [Fintype G] [Group G] [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a b : GroupAlgebraElement G) : Prop :=
  forall v : V,
    repOfGroupAlgebraElement rep a (repOfGroupAlgebraElement rep b v) =
      repOfGroupAlgebraElement rep b (repOfGroupAlgebraElement rep a v)

/-- A coefficient-central element commutes, after applying a representation,
with every represented group-algebra element. -/
theorem repOfGroupAlgebraElements_commute_of_central
    {G V : Type*} [Fintype G] [Group G]
    [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData G V)
    (a b : GroupAlgebraElement G)
    (hcentral : a.IsCentralByCoefficients) :
    RepElementsCommute rep a b := by
  classical
  intro v
  let A : V →ₗ[Real] V := repOfGroupAlgebraElementLinearMap rep a
  have hgroup := repOfGroupAlgebraElement_commutes_of_central rep a hcentral
  change A (repOfGroupAlgebraElement rep b v) =
    repOfGroupAlgebraElement rep b (A v)
  unfold repOfGroupAlgebraElement
  calc
    A (∑ g : G, b g • rep.rho g v) =
        ∑ g : G, A (b g • rep.rho g v) := by
      rw [map_sum]
    _ = ∑ g : G, b g • A (rep.rho g v) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [map_smul]
    _ = ∑ g : G, b g • rep.rho g (A v) := by
      apply Finset.sum_congr rfl
      intro g _hg
      congr 1
      change repOfGroupAlgebraElement rep a (rep.rho g v) =
        rep.rho g (repOfGroupAlgebraElement rep a v)
      exact hgroup g v

/-- A Young-block representation-action interface.  It identifies adjacent
Young operators and diagonal content operators with represented group-algebra
objects, but it does not assert scalarity of any averaged matching operator. -/
structure YoungRepresentationActionData {n : Nat}
    (lam : YoungDiagram (n + 1)) where
  rep :
    GroupRepresentationActionData (Perm (Fin (n + 1))) (TableauSpace lam)
  adjacentPerm : Fin n -> Perm (Fin (n + 1))
  rho_adjacent :
    forall a : Fin n, forall f : TableauSpace lam,
      rep.rho (adjacentPerm a) f = youngAdjacentOperator a f
  jucysMurphyElement :
    Fin (n + 1) -> GroupAlgebraElement (Perm (Fin (n + 1)))
  rho_content :
    forall a : Fin (n + 1), forall f : TableauSpace lam,
      repOfGroupAlgebraElement rep (jucysMurphyElement a) f =
        jucysMurphyDiagonalOperator a f

/-- The operator on a Young block produced by a group-algebra element through a
Young representation-action interface. -/
def averagedRejectionYoungOperatorOfGroupAlgebra {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (q : GroupAlgebraElement (Perm (Fin (n + 1)))) :
    TableauSpace lam -> TableauSpace lam :=
  repOfGroupAlgebraElement young.rep q

/-- If `rho(q)` commutes with every represented group element, then in
particular it commutes with every adjacent Young operator identified by the
Young representation-action interface. -/
theorem averagedRejectionYoungOperatorOfGroupAlgebra_commutes_adjacent
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (q : GroupAlgebraElement (Perm (Fin (n + 1))))
    (hcomm : RepElementCommutesWithGroupAction young.rep q)
    (a : Fin n) (f : TableauSpace lam) :
    averagedRejectionYoungOperatorOfGroupAlgebra young q
        (youngAdjacentOperator a f) =
      youngAdjacentOperator a
        (averagedRejectionYoungOperatorOfGroupAlgebra young q f) := by
  unfold averagedRejectionYoungOperatorOfGroupAlgebra
  rw [<- young.rho_adjacent a f]
  rw [hcomm (young.adjacentPerm a) f]
  rw [young.rho_adjacent a (repOfGroupAlgebraElement young.rep q f)]

/-- If `rho(q)` commutes with the group-algebra element realizing the content
operator, then it commutes with the corresponding diagonal content operator. -/
theorem averagedRejectionYoungOperatorOfGroupAlgebra_commutes_content
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (q : GroupAlgebraElement (Perm (Fin (n + 1))))
    (hcomm :
      forall a : Fin (n + 1),
        RepElementsCommute young.rep q (young.jucysMurphyElement a))
    (a : Fin (n + 1)) (f : TableauSpace lam) :
    averagedRejectionYoungOperatorOfGroupAlgebra young q
        (jucysMurphyDiagonalOperator a f) =
      jucysMurphyDiagonalOperator a
        (averagedRejectionYoungOperatorOfGroupAlgebra young q f) := by
  unfold averagedRejectionYoungOperatorOfGroupAlgebra
  rw [<- young.rho_content a f]
  rw [hcomm a f]
  rw [young.rho_content a (repOfGroupAlgebraElement young.rep q f)]

/-- A group-algebra representation-action package instantiates the
`AveragedRejectionYoungOperatorData` interface once the represented element is
known to commute with adjacent group actions and with the represented
Jucys--Murphy/content elements. -/
def averagedRejectionYoungOperatorData_of_groupAlgebraAction {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (q : GroupAlgebraElement (Perm (Fin (n + 1))))
    (hgroup : RepElementCommutesWithGroupAction young.rep q)
    (hcontent :
      forall a : Fin (n + 1),
        RepElementsCommute young.rep q (young.jucysMurphyElement a)) :
    AveragedRejectionYoungOperatorData lam where
  operator := averagedRejectionYoungOperatorOfGroupAlgebra young q
  map_add := by
    intro f g
    change repOfGroupAlgebraElement young.rep q (f + g) =
      repOfGroupAlgebraElement young.rep q f +
        repOfGroupAlgebraElement young.rep q g
    exact repOfGroupAlgebraElement_map_add young.rep q f g
  map_smul := by
    intro c f
    change repOfGroupAlgebraElement young.rep q (c • f) =
      c • repOfGroupAlgebraElement young.rep q f
    exact repOfGroupAlgebraElement_map_smul young.rep q c f
  commutes_adjacent := by
    exact averagedRejectionYoungOperatorOfGroupAlgebra_commutes_adjacent
      young q hgroup
  commutes_content := by
    exact averagedRejectionYoungOperatorOfGroupAlgebra_commutes_content
      young q hcontent

/-- A coefficient-central group-algebra element automatically supplies both
commutation fields required by the averaged-rejection Young-operator
interface. -/
def averagedRejectionYoungOperatorData_of_centralGroupAlgebraElement
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (q : GroupAlgebraElement (Perm (Fin (n + 1))))
    (hcentral : q.IsCentralByCoefficients) :
    AveragedRejectionYoungOperatorData lam :=
  averagedRejectionYoungOperatorData_of_groupAlgebraAction young q
    (repOfGroupAlgebraElement_commutes_of_central young.rep q hcentral)
    (fun a =>
      repOfGroupAlgebraElements_commute_of_central young.rep q
        (young.jucysMurphyElement a) hcentral)

end DictatorshipTesting
