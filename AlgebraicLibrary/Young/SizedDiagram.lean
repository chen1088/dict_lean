import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Young diagrams of a fixed size

Mathlib's `YoungDiagram` is unindexed.  This thin subtype supplies the size
index convenient in representation theory while retaining Mathlib's diagram
implementation and theorem ecosystem.
-/

namespace AlgebraicLibrary

/-- A Mathlib Young diagram with exactly `n` cells. -/
abbrev SizedYoungDiagram (n : ℕ) :=
  { μ : _root_.YoungDiagram // μ.card = n }

namespace SizedYoungDiagram

/-- The finite type of cells of a sized Young diagram. -/
abbrev Cell {n : ℕ} (μ : SizedYoungDiagram n) := ↥μ.1.cells

@[simp] theorem card_cells {n : ℕ} (μ : SizedYoungDiagram n) :
    Fintype.card μ.Cell = n := by
  simpa [Cell] using μ.2

@[simp] theorem val_card {n : ℕ} (μ : SizedYoungDiagram n) :
    μ.1.card = n :=
  μ.2

/-- Forget the size witness. -/
def forget {n : ℕ} : SizedYoungDiagram n → _root_.YoungDiagram :=
  Subtype.val

@[simp] theorem forget_apply {n : ℕ} (μ : SizedYoungDiagram n) :
    forget μ = μ.1 := rfl

end SizedYoungDiagram

end AlgebraicLibrary
