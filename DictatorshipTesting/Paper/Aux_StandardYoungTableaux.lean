import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-!
# Standard Young tableaux

This file contains the concrete tableau vocabulary needed by Definition 5.9:
cells of a Young diagram, standard Young tableaux, and the set of tableaux whose
maximum entry lies in a specified cell.  It does not introduce the later
Hilbert-space/span version of the deletion spaces.
-/

noncomputable section

namespace DictatorshipTesting

/-- A cell of a Young diagram. -/
abbrev YoungCell {n : Nat} (lam : YoungDiagram n) :=
  {u : Fin n × Fin n // u ∈ youngCells lam}

namespace YoungCell

/-- Row coordinate of a Young cell. -/
def row {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) : Nat :=
  (u.1.1 : Nat)

/-- Column coordinate of a Young cell. -/
def col {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) : Nat :=
  (u.1.2 : Nat)

/-- A Young cell as a pair of natural coordinates. -/
def toNatPair {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) : Nat × Nat :=
  (row u, col u)

/-- A `YoungCell` is a box of the underlying Young diagram. -/
theorem isYoungBox {n : Nat} {lam : YoungDiagram n} (u : YoungCell lam) :
    IsYoungBox lam (toNatPair u) := by
  rcases u with ⟨⟨r, c⟩, hcell⟩
  simpa [toNatPair, row, col, IsYoungBox, youngCells]
    using (Finset.mem_filter.mp hcell).2

end YoungCell

/-- A standard Young tableau of shape `lam`, with entries `0, ..., n-1`.
This is the zero-indexed version of the paper's entries `1, ..., n`. -/
structure StandardYoungTableau {n : Nat} (lam : YoungDiagram n) where
  entry : YoungCell lam -> Fin n
  bijective : Function.Bijective entry
  row_strict :
    forall {u v : YoungCell lam},
      YoungCell.row u = YoungCell.row v ->
      YoungCell.col u < YoungCell.col v ->
      entry u < entry v
  col_strict :
    forall {u v : YoungCell lam},
      YoungCell.col u = YoungCell.col v ->
      YoungCell.row u < YoungCell.row v ->
      entry u < entry v

/-- The maximum entry of a tableau of size `n+1` is in cell `u`. -/
def TableauMaxAt {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (u : YoungCell lam) : Prop :=
  T.entry u = Fin.last n

/-- Set-level version of the one-box deletion space: tableaux whose maximum
entry lies in `u`. The Hilbert-space span will be added later. -/
def OneBoxDeletionTableaux {n : Nat} (lam : YoungDiagram (n + 1))
    (u : YoungCell lam) : Set (StandardYoungTableau lam) :=
  {T | TableauMaxAt T u}

/-- Membership in the set-level one-box deletion space is the maximum-entry
condition. -/
theorem mem_oneBoxDeletionTableaux_iff {n : Nat}
    {lam : YoungDiagram (n + 1)} {u : YoungCell lam}
    {T : StandardYoungTableau lam} :
    T ∈ OneBoxDeletionTableaux lam u <-> TableauMaxAt T u := by
  rfl

end DictatorshipTesting
