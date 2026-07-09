import DictatorshipTesting.Paper.S05_Int_StandardYoungTableaux

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Definition 5.12 (`def:one-box-deletion-spaces`)
Title in paper: One-box deletion spaces.

Status: definition/interface. The set-level tableau deletion spaces are formalized below.  The
Hilbert-space span version used later in the tableau proof is future work.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.11, set-level tableau deletion space. -/
abbrev S05_Def5_12_OneBoxDeletionTableaux {n : Nat}
    (lam : YoungDiagram (n + 1)) (u : YoungCell lam) :
    Set (StandardYoungTableau lam) :=
  OneBoxDeletionTableaux lam u

/-- Definition 5.11, maximum-entry condition. -/
abbrev S05_Def5_12_TableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (u : YoungCell lam) : Prop :=
  TableauMaxAt T u

/-- Membership in the set-level deletion space is the maximum-entry condition. -/
theorem S05_Def5_12_mem_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {u : YoungCell lam}
    {T : StandardYoungTableau lam} :
    T ∈ S05_Def5_12_OneBoxDeletionTableaux lam u <->
      S05_Def5_12_TableauMaxAt T u := by
  rfl

/-- Definition 5.11 set-level component: every standard tableau has a unique
maximum-entry cell. -/
theorem S05_Def5_12_existsUnique_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam, S05_Def5_12_TableauMaxAt T u := by
  exact existsUnique_tableauMaxAt T

end DictatorshipTesting
