# AlgebraicLibrary

`AlgebraicLibrary` is the reusable layer extracted from the dictatorship-testing
formalization. It is a separate `lean_lib` beside `DictatorshipTesting`.

Dependency rule:

```text
Mathlib  <-  AlgebraicLibrary  <-  DictatorshipTesting
```

Nothing under this directory may import a `DictatorshipTesting` module.

## Build and incremental cache

Build the reusable layer before working on paper modules:

```bash
lake exe cache get
lake build AlgebraicLibrary
lake build DictatorshipTesting
```

Lake stores compiled `.olean` artifacts under `.lake/build`. Because
`AlgebraicLibrary` is a separate `lean_lib`, an unchanged library is reused by
later `DictatorshipTesting` and focused-module builds. Lake's reported job count
includes dependencies it checked; a cached run with no `Built` lines did not
recompile the library.

## Module map

- `BooleanCube`: Boolean cubes over an arbitrary coordinate type, XOR/flip
  operations, Walsh characters, uniform expectation, Fourier inversion,
  Parseval, and arbitrary low-degree truncation.
- `PropertyTesting`: finite-seed nonadaptive testers over arbitrary query and
  answer types, plus independent repetition and exact acceptance/rejection
  formulas.
- `Combinatorics.OrderedMatching`: ordered matchings, optional edge swaps,
  coordinate-dependence, and the XOR-to-permutation homomorphism.
- `Order.LinearExtension`: connectivity of finite list-level linear extensions
  by adjacent swaps of incomparable entries.
- `Algebra.OperatorProduct`: fixed-order products of Boolean-selected
  commuting involutions, including XOR and simultaneous-eigenvector formulas.
- `Young.SizedDiagram`: a size subtype of Mathlib's global `YoungDiagram`.
- `Young.IndexedDiagram`: the finite-coordinate row model used in explicit
  tableau calculations, together with a row-preserving conversion to Mathlib's
  `YoungDiagram`.
- `Young.DiagramCorners`, `Young.StandardTableau`, and
  `Young.TableauDimension`: corner deletion/insertion, standard tableaux, and
  one- and two-box branching combinatorics.
- `Young.TableauSumOfSquares`: Young-lattice path counting and the tableau
  square-sum identity.
- `Young.AdjacentEntries`, `Young.OrthogonalRepresentation`,
  `Young.OrthogonalActionData`, `Young.AdjacentWord`, and
  `Young.AdjacentCoxeterPresentation`: adjacent tableau swaps, explicit Young
  orthogonal operators, reusable group/group-algebra action data, and the
  type-A Coxeter presentation extending them to permutations.
- `Young.JucysMurphyActionData`, `Young.JucysMurphyContentAction`, and
  `Young.TableauTrace`: Jucys--Murphy coefficient/action formulas and
  tableau-coordinate trace identities.

The paper tree retains numbered theorem and lemma modules. Reusable definitions
and internal lemmas are referenced directly from this library; there is no
parallel paper-side forwarding file for each library module.

The boundary is intentional. Canonical and arbitrary matching constructions,
matching characters and idempotents, matching restriction/eigenbasis results,
averaged rejection and local truncation, `U1`/block-energy bridges, and the
even/odd certificate arguments remain in `DictatorshipTesting` because they
encode the dictatorship test rather than reusable algebraic infrastructure.
