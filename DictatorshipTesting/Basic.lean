import Mathlib

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.AlgebraicProperty.Aux_SumIfMemPerm`
- `DictatorshipTesting.Basic.Aux_NatIndicatorMul`
- `DictatorshipTesting.Basic.Aux_PcompApply`
- `DictatorshipTesting.Basic.Aux_PswapSelfLeft`
- `DictatorshipTesting.Basic.Aux_PswapSelfRight`
- `DictatorshipTesting.Basic.Aux_RowDictAsCosetSumEqRowDict`
- `DictatorshipTesting.Paper.Defs`
-/


/-!
# Basic objects for dictatorship testing over `S_n`

The paper works with permutations of `[n]`.  In Lean it is cleaner to state the
basic algebra for an arbitrary finite type `α`; the intended specialization is
`α = Fin n`.

This file intentionally keeps the first formalization elementary: no
representation theory, no Fourier analysis, and no probability yet.
-/

open scoped BigOperators

namespace DictatorshipTesting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The symmetric group on a finite type.  For the paper, use `Perm (Fin n)`. -/
abbrev Perm (α : Type*) := Equiv.Perm α

/-- Composition of permutations in the paper's convention: `(σ ∘p τ) x = σ (τ x)`. -/
def pcomp (σ τ : Perm α) : Perm α := τ.trans σ

infixr:80 " ∘p " => pcomp

/-- The transposition swapping `a` and `b`. -/
def pswap (a b : α) : Perm α := Equiv.swap a b

/-- The indicator of the one-coset `T_{ij} = {π : π i = j}`. -/
def oneCoset (i j : α) (π : Perm α) : ℕ :=
  if π i = j then 1 else 0

/-- A row dictator: the indicator of `⋃_{j ∈ J} T_{ij}`. -/
def rowDict (i : α) (J : Finset α) (π : Perm α) : ℕ :=
  if π i ∈ J then 1 else 0

/-- The paper's summation notation for the same row dictator. -/
def rowDictAsCosetSum (i : α) (J : Finset α) (π : Perm α) : ℕ :=
  ∑ j ∈ J, oneCoset i j π

/-- A column dictator: the indicator of `⋃_{i ∈ I} T_{ij}`.  It is not needed for
`eq:algebraic_property`, but it records the other half of the paper's definition. -/
def colDict (I : Finset α) (j : α) (π : Perm α) : ℕ :=
  if π.symm j ∈ I then 1 else 0

end DictatorshipTesting
