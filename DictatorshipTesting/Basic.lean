import Mathlib

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S02_IntDef_BoolFn`
-/
/-!
# Basic objects for dictatorship testing over `S_n`

The paper works with permutations of `[n]`.  In Lean it is cleaner to state the
basic algebra for an arbitrary finite type `α`; the intended specialization is
`α = Fin n`.

This file intentionally keeps the first formalization elementary: no
representation theory, no Fourier analysis, and no probability yet.
-/

namespace DictatorshipTesting

variable {α : Type*} [DecidableEq α]

/-- The symmetric group on a finite type.  For the paper, use `Perm (Fin n)`. -/
abbrev Perm (α : Type*) := Equiv.Perm α

/-- The transposition swapping `a` and `b`. -/
def pswap (a b : α) : Perm α := Equiv.swap a b

end DictatorshipTesting
