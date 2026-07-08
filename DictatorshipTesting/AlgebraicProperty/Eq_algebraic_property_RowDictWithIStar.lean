import DictatorshipTesting.AlgebraicProperty.Eq_algebraic_property_RowDict

/-
Direct reverse imports:
- `DictatorshipTesting.AlgebraicProperty`
-/


open scoped BigOperators

namespace DictatorshipTesting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Same algebraic property but with the paper's `iStar` parameter explicit.

The paper says `(iStar,jStar) ∈ S`, where `S = {(i,j) : j ∈ J}`.  Therefore
`iStar = i` and `jStar ∈ J`.  We encode that directly as hypotheses.
-/
theorem algebraic_property_rowDict_with_iStar
    (i iStar : α) (J : Finset α) (jStar : α)
    (hiStar : iStar = i) (hjStar : jStar ∈ J)
    (π1 π2 : Perm α) :
    (∑ j ∈ J,
        rowDict i J ((pswap (π1.symm j) jStar) ∘p π2))
      =
    (∑ k : α,
        rowDict i J (π1 ∘p (pswap iStar k)) *
        rowDict i J ((pswap k jStar) ∘p π2)) := by
  subst iStar
  exact algebraic_property_rowDict i J jStar hjStar π1 π2

end DictatorshipTesting
