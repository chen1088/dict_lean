import DictatorshipTesting.Paper.Aux_StandardYoungTableaux

/-!
# Tableau-count dimension

This helper file defines an assumption-free dimension proxy by counting standard
Young tableaux.  It is parallel to the hook-length `youngDim` definition in
`Defs.lean`; no Specht-module dimension theorem is asserted here.
-/

noncomputable section

namespace DictatorshipTesting

noncomputable instance standardYoungTableauFintype {n : Nat}
    (lam : YoungDiagram n) : Fintype (StandardYoungTableau lam) := by
  classical
  exact Fintype.ofInjective
    (fun T : StandardYoungTableau lam => T.entry)
    (by
      intro T S h
      exact standardYoungTableau_ext_entry (by
        intro u
        exact congrFun h u))

noncomputable instance tableauMaxAtSubtypeFintype {n : Nat}
    {lam : YoungDiagram (n + 1)} (u : YoungCell lam) :
    Fintype {T : StandardYoungTableau lam // TableauMaxAt T u} := by
  classical
  infer_instance

/-- Assumption-free tableau-count dimension. -/
def tableauDimNat {n : Nat} (lam : YoungDiagram n) : Nat :=
  Fintype.card (StandardYoungTableau lam)

/-- Real-valued tableau-count dimension. -/
def tableauDim {n : Nat} (lam : YoungDiagram n) : ℝ :=
  tableauDimNat lam

theorem tableauDimNat_eq_card {n : Nat} (lam : YoungDiagram n) :
    tableauDimNat lam = Fintype.card (StandardYoungTableau lam) := by
  rfl

theorem tableauDim_nonneg {n : Nat} (lam : YoungDiagram n) :
    0 <= tableauDim lam := by
  simp [tableauDim]

theorem card_tableaux_maxAt_deletedCorner_eq_child
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    Fintype.card
        {T : StandardYoungTableau lam //
          TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)}
      =
    Fintype.card (StandardYoungTableau mu) := by
  classical
  exact Fintype.card_congr
    (oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow h hr)

theorem tableauDim_fixed_oneBoxChild
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    ((Fintype.card
        {T : StandardYoungTableau lam //
          TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)} : Nat) : ℝ)
      =
    tableauDim mu := by
  rw [tableauDim, tableauDimNat,
    card_tableaux_maxAt_deletedCorner_eq_child h hr]

end DictatorshipTesting
