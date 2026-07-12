import DictatorshipTesting.Paper.S05_Int_StandardYoungTableaux
import DictatorshipTesting.Paper.Defs.S05_Def5_02_RemovableCorners
import DictatorshipTesting.Paper.Defs.S05_Def5_03_StandardTableaux

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_14_OneBoxDecompositionAndDeletion`
-/


/-!
Paper statement: Definition 5.9 `def:one-box-deletion-spaces`
Title in paper: One-box deletion spaces.

Status: definition/interface. The set-level tableau deletion spaces below
provide the coordinate indexing used by Lemmas 5.14--5.16.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.9, set-level tableau deletion space. -/
abbrev S05_Def5_09_OneBoxDeletionTableaux {n : Nat}
    (lam : YoungDiagram (n + 1)) (u : YoungCell lam) :
    Set (StandardYoungTableau lam) :=
  OneBoxDeletionTableaux lam u

/-- Definition 5.9, maximum-entry condition. -/
abbrev S05_Def5_09_TableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (u : YoungCell lam) : Prop :=
  TableauMaxAt T u

/-- Membership in the set-level deletion space is the maximum-entry condition. -/
theorem S05_Def5_09_mem_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {u : YoungCell lam}
    {T : StandardYoungTableau lam} :
    T ∈ S05_Def5_09_OneBoxDeletionTableaux lam u <->
      S05_Def5_09_TableauMaxAt T u := by
  rfl

/-- Definition 5.9 set-level component: every standard tableau has a unique
maximum-entry cell. -/
theorem S05_Def5_09_existsUnique_tableauMaxAt {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    ∃! u : YoungCell lam, S05_Def5_09_TableauMaxAt T u := by
  exact existsUnique_tableauMaxAt T

end DictatorshipTesting
