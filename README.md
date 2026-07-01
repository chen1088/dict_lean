# DictatorshipTesting

Lean 4 + Mathlib scaffold for formalizing elementary and finite-dimensional
parts of a dictatorship-testing paper for Boolean functions on `S_n`.

The project is intentionally organized around the paper.  Numbered theorem,
lemma, proposition, and corollary files use the paper number in the filename,
for example `Thm1_1_MainIntro.lean`, `L4_13_OneTrialSoundness.lean`, and
`Prop4_12_SquareEnergyControlsGlobalDegree.lean`.  Helper files that exist only
to support the Lean development use the prefix `Aux_`.

## Build

This checkout uses the Lean toolchain in `lean-toolchain`:

```text
leanprover/lean4:v4.32.0-rc1
```

To build the full library:

```bash
cd dict_lean
lake exe cache get
lake build DictatorshipTesting
```

The current full target builds successfully.

## Current Status

The scaffold contains real Lean proofs for the elementary Boolean-cube,
matching-cube, and averaging steps that have been formalized so far.  A small
number of hard results are intentionally isolated behind named aux declarations
with `sorry`.

Current intentional assumptions:

External structural inputs:

- `Aux_BooleanU1StructuralInput.lean`: the external classification of Boolean
  degree-one functions on `S_n`.
- `Aux_FKNStabilityInput.lean`: the external FKN/stability theorem on `S_n`.
- `Aux_MatchingRestrictionInput.lean`: the Specht/Pieri-Littlewood-Richardson
  restriction data for matching subgroups, represented by the scalar
  consequences currently visible in Lean.
- `Aux_YoungDimensionBranchingInput.lean`: the dimension shadow of the
  two-strip Pieri/Littlewood-Richardson branching rule, stated as
  `youngDim_twoStrip_branching_input`.
- `Aux_SpectralGapFromCertificates.lean`: the remaining Young-block spectral
  decomposition, Schur-lemma scalarity, and identification of the `U1` summand
  needed to turn block certificate inequalities into the global matching
  spectral gap.

Internal finite certificate obligations:

- `Aux_ZBoundFiniteInduction.lean`: the finite Young-diagram induction behind
  Lemma 5.4.  This file now proves the induction skeleton, including the base
  case and the generic non-exceptional step, modulo the branching input above
  and explicit remaining exceptional-shape facts for `(2m-1,1)` and
  `(2m-2,2)`.
- `Aux_HEvenFiniteInduction.lean`: the finite Young-diagram induction behind
  Lemma 5.5.
- `Aux_HOddFiniteInduction.lean`: the finite Young-diagram induction behind
  Lemma 5.6.

Proven bridge components:

- `Aux_LocalCharacterProjection.lean`: local matching projection preserves
  matching-cube characters of weight `0` or `1` and kills characters of weight
  at least `2`.
- `Aux_TraceLocalTruncation.lean`: scalar trace formula with factor
  `youngDim lam * hEven m lam` or `youngDim lam * hOdd m lam`, conditional on
  the matching-restriction input.
- `Aux_CentralizationBridge.lean`: trace-divided-by-block-dimension algebra,
  giving the scalar `h_m(lambda) / d_lambda` once scalarity and the trace
  identity are available.

The paper-numbered files `Thm2_1`, `Thm2_2`, `L5_4`, `L5_5`, and `L5_6` are
therefore clean wrappers around explicit assumptions rather than places where
large hidden proof obligations are buried.

## Layout

Root import indexes:

- `DictatorshipTesting.lean`: imports the whole project.
- `DictatorshipTesting/BasicFacts.lean`: imports elementary permutation facts.
- `DictatorshipTesting/SetFacts.lean`: finite set operations used in early
  algebraic identities.
- `DictatorshipTesting/AlgebraicProperty.lean`: imports the elementary
  row-dictator algebraic property files.
- `DictatorshipTesting/Paper.lean`: imports paper-numbered theorem files and
  their helper index.
- `DictatorshipTesting/PaperAux.lean`: imports helper-only paper modules so the
  full library build checks them.
- `DictatorshipTesting/PaperPlaceholders.lean`: imports the numbered paper
  files that are currently represented in the scaffold.

Core paper definitions:

- `DictatorshipTesting/Paper/Defs.lean`: shared definitions for Boolean
  functions on permutations, dictators, `U1`, distances, matching cubes,
  square-test quantities, local projections, near-perfect matchings, and the
  finite Young-diagram model used in Section 5.

Elementary files:

- `DictatorshipTesting/Basic.lean`: permutation conventions, transpositions,
  one-coset indicators, and row/column dictator indicators.
- `DictatorshipTesting/SetFacts.lean`: set difference and symmetric difference.
- `DictatorshipTesting/AlgebraicProperty/*.lean`: finite reindexing and the
  row-dictator algebraic-property identity.

Paper-numbered highlights:

- `Thm1_1_MainIntro.lean`: main tester statement, currently routed through the
  abstract tester-amplification interface.
- `Thm2_1_BooleanU1.lean`: Boolean degree-one structural input.
- `Thm2_2_FKNInput.lean`: FKN/stability input.
- `L2_3_*`: cube-character orthonormality, Fourier expansion, and Parseval.
- `L3_1_DictatorToJunta.lean` and `L3_2_PerfectCompleteness.lean`: matching
  cube completeness side.
- `L4_1` through `L4_13`: matching-cube soundness reductions up to the
  one-trial soundness bound.
- `L5_1` through `L5_6`: spectral-gap and finite certificate scaffold.

## Naming Conventions

- `ThmA_B_...`: Theorem A.B in the paper.
- `LA_B_...`: Lemma A.B in the paper, written without the space as
  `L4_13_...`.
- `PropA_B_...`: Proposition A.B.
- `CorA_B_...`: Corollary A.B.
- `Aux_...`: Lean helper lemma, implementation detail, or isolated external
  input.

Keep theorem names stable when possible.  If a theorem is paper-numbered, keep
the declaration in the paper-numbered file even when the hard proof is factored
into an aux file.

## Development Notes

Useful commands:

```bash
lake build DictatorshipTesting
lake build DictatorshipTesting.Paper.L5_4_ZBoundApp
rg "sorry" DictatorshipTesting
```

The project uses `sorry` only for deliberately isolated hard inputs.  When a
new `sorry` is needed, prefer making it a named theorem in an `Aux_...` file and
then proving the paper-numbered result by applying that named theorem.  This
keeps the dependency graph readable and makes the remaining mathematical
obligations easy to find.

Do not attempt to hide representation theory inside elementary files.  The
current boundary is:

- finite cube and matching identities are formalized directly;
- external stability and representation-theoretic statements are isolated;
- Section 5 finite Young-diagram inequalities are separated from the spectral
  bridge.
