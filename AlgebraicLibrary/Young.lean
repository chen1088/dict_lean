import AlgebraicLibrary.Young.SizedDiagram
import AlgebraicLibrary.Young.IndexedDiagram
import AlgebraicLibrary.Young.DiagramCorners
import AlgebraicLibrary.Young.StandardTableau
import AlgebraicLibrary.Young.TableauDimension
import AlgebraicLibrary.Young.AdjacentEntries
import AlgebraicLibrary.Young.OrthogonalRepresentation
import AlgebraicLibrary.Young.OrthogonalActionData
import AlgebraicLibrary.Young.AdjacentWord
import AlgebraicLibrary.Young.AdjacentCoxeterPresentation
import AlgebraicLibrary.Young.JucysMurphyActionData
import AlgebraicLibrary.Young.JucysMurphyContentAction
import AlgebraicLibrary.Young.TableauSumOfSquares
import AlgebraicLibrary.Young.TableauTrace
import Mathlib.RepresentationTheory.Character

/-!
# Young diagrams and representation-theory boundary

This library exposes both Mathlib's global `YoungDiagram` through
`SizedYoungDiagram` and the finite-coordinate `IndexedYoungDiagram` used by
explicit tableau computations.  Conversion lemmas keep the two presentations
at a deliberate boundary rather than letting project code define either one.
-/
