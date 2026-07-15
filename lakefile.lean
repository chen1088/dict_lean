import Lake

/-
Direct reverse imports:
- none
-/
open Lake DSL

package «dict_lean» where
  -- This project is intended for a standard Lean 4 + mathlib setup.
  -- After installing Lean, run:
  --   lake exe cache get
  --   lake build

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib DictatorshipTesting where

/-- Reusable algebraic, combinatorial, Fourier, and representation-theoretic
infrastructure factored out of the dictatorship-testing development. -/
lean_lib AlgebraicLibrary where
