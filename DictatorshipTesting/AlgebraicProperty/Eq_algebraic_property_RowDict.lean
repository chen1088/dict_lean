import DictatorshipTesting.AlgebraicProperty.Aux_SumIfMemPerm
import DictatorshipTesting.Basic.Aux_PcompApply

/-
Direct reverse imports:
- `DictatorshipTesting.AlgebraicProperty`
- `DictatorshipTesting.AlgebraicProperty.Eq_algebraic_property_RowDictWithIStar`
-/
/-!
# Algebraic property for row dictators

This file states the Lean version of the paper's equation
`eq:algebraic_property` for a row dictator.
-/

open scoped BigOperators

namespace DictatorshipTesting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A cleaned-up theorem statement for equation `eq:algebraic_property`.

Paper notation:

* `α` is `[n]`;
* `π1`, `π2` are permutations in `S_n`;
* `J` is the set of accepting images for the dictator;
* `rowDict i J` is `χ = ∑_{j ∈ J} T_{i,j}`;
* `jStar ∈ J`, so `(i,jStar)` is in the representative set `S_χ`;
* `pswap a b` is the transposition `π_{a ↔ b}`;
* `σ ∘p τ` means `σ ∘ τ`.
-/
theorem algebraic_property_rowDict
    (i : α) (J : Finset α) (jStar : α) (_hjStar : jStar ∈ J)
    (π1 π2 : Perm α) :
    (∑ j ∈ J,
        rowDict i J ((pswap (π1.symm j) jStar) ∘p π2))
      =
    (∑ k : α,
        rowDict i J (π1 ∘p (pswap i k)) *
        rowDict i J ((pswap k jStar) ∘p π2)) := by
  classical
  have hRhsReindex :
      (∑ k : α,
          rowDict i J (π1 ∘p (pswap i k)) *
          rowDict i J ((pswap k jStar) ∘p π2)) =
        ∑ j ∈ J,
          rowDict i J ((pswap (π1.symm j) jStar) ∘p π2) := by
    calc
      (∑ k : α,
          rowDict i J (π1 ∘p (pswap i k)) *
          rowDict i J ((pswap k jStar) ∘p π2))
          = ∑ k : α,
              (if π1 k ∈ J then
                (if pswap k jStar (π2 i) ∈ J then 1 else 0)
               else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases h₁ : π1 k ∈ J <;>
            by_cases h₂ : pswap k jStar (π2 i) ∈ J <;>
            simp [rowDict, pcomp_apply, pswap, h₁]
      _ = ∑ j ∈ J,
              (if pswap (π1.symm j) jStar (π2 i) ∈ J then 1 else 0) := by
            simpa using
              (sum_if_mem_perm π1 J
                (fun k => if pswap k jStar (π2 i) ∈ J then 1 else 0))
      _ = ∑ j ∈ J,
              rowDict i J ((pswap (π1.symm j) jStar) ∘p π2) := by
            apply Finset.sum_congr rfl
            intro j _
            simp [rowDict, pcomp_apply]
  exact hRhsReindex.symm

end DictatorshipTesting
