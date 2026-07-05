import DictatorshipTesting.Paper.Aux_StandardYoungTableaux

/-!
Paper statement: Definition 5.8 (`def:one-box-deletion-spaces`)
Title in paper: One-box deletion spaces.

Status: the set-level tableau deletion spaces are formalized below.  The
Hilbert-space span version used later in the tableau proof is future work.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.9, set-level tableau deletion space. -/
abbrev S05_Def5_08_OneBoxDeletionTableaux {n : Nat}
    (lam : YoungDiagram (n + 1)) (u : YoungCell lam) :
    Set (StandardYoungTableau lam) :=
  OneBoxDeletionTableaux lam u

/-- Definition 5.9, maximum-entry condition. -/
abbrev S05_Def5_08_TableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (u : YoungCell lam) : Prop :=
  TableauMaxAt T u

/-- Membership in the set-level deletion space is the maximum-entry condition. -/
theorem S05_Def5_08_mem_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {u : YoungCell lam}
    {T : StandardYoungTableau lam} :
    T ∈ S05_Def5_08_OneBoxDeletionTableaux lam u <->
      S05_Def5_08_TableauMaxAt T u := by
  rfl

/-- Definition 5.9 set-level component: every standard tableau has a unique
maximum-entry cell. -/
theorem S05_Def5_08_existsUnique_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam, S05_Def5_08_TableauMaxAt T u := by
  exact existsUnique_tableauMaxAt T

end DictatorshipTesting
