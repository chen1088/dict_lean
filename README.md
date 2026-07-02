# DictatorshipTesting

Lean 4 + Mathlib scaffold for formalizing elementary and finite-dimensional
parts of a dictatorship-testing paper for Boolean functions on `S_n`.

The project is intentionally organized around the paper.  Numbered theorem,
lemma, proposition, and corollary files use the paper number in the filename,
for example `S01_Thm1_01_MainIntro.lean`, `S04_Lem4_13_OneTrialSoundness.lean`, and
`S04_Prop4_12_SquareEnergyControlsGlobalDegree.lean`.  Helper files that exist only
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

Current proof-status map:

Section 2 external structural inputs:

- `S02_Thm2_01_BooleanU1Classification.lean` -- Theorem 2.1
  (`thm:boolean-u1`): external classification direction
  `boolFnToReal f ∈ U1 (Fin n) -> IsDictator f` for `3 <= n`.  The `n = 1`
  and `n = 2` cases, and the converse direction that dictators lie in `U1`,
  are proved directly.
- `S02_Thm2_02_FKNStability.lean` -- Theorem 2.2 (`thm:fkn-input`):
  external FKN/stability theorem on `S_n`, stated only for the `4 <= n`
  range used by the one-trial soundness proof.

Section 5 standard representation-theoretic inputs:

- `S05_Lem5_01_TwoStripDimensionRecursion.lean` -- Lemma 5.1
  (`lem:dimension-two-strip-recurrence`): two-strip
  Pieri/Littlewood-Richardson dimension recursion.
- `S05_Lem5_02_OneBoxDimensionRecursion.lean` -- Lemma 5.2
  (`lem:dimension-one-box-recurrence`): ordinary one-box dimension recursion.
  The `m = 0` and `m = 1` cases are proved directly; the remaining input is the
  `2 <= m` branching statement `youngDim_oneBox_branching_positive_input`.
- `S05_Lem5_03_MatchingRestrictionPieri.lean` -- Lemma 5.3
  (`lem:matching-restriction-X`): the current Lean scalar consequence
  `0 <= h <= youngDim` is proved from the finite certificate bounds.  The full
  Specht-module restriction decomposition is not yet represented as a Lean
  object.

Section 5 derived bridge components:

- `S05_Lem5_04_LocalTruncationCharacterProjection.lean` -- Lemma 5.4
  (`lem:PM-character-projection`): proved matching-cube character projection.
- `S05_Lem5_05_TraceLocalTruncation.lean` -- Lemma 5.5
  (`lem:PM-trace-young-block`): trace formula conditional on Lemma 5.3.
- `S05_Lem5_06_CentralizationOverMatchings.lean` -- Lemma 5.6
  (`lem:centralization-matchings`): trace-divided-by-dimension algebra, with
  Young-block scalarity isolated in Lemma 5.8.
- `S05_Lem5_08_SpectralBridgeFromCertificates.lean` -- Lemma 5.8
  (`lem:spectral-certificate`): remaining Young-block spectral bridge input,
  stated in the `2 <= m` range used by the `n >= 4` matching-gap theorem.

Section 5 finite certificates:

- `S05_Lem5_10_ZBoundCertificate.lean` -- Lemma 5.10 (`lem:z-bound-app`):
  finite `zEven` certificate, proved modulo Lemma 5.1.
- `S05_Lem5_12_EvenHCertificate.lean` -- Lemma 5.12 (`lem:h-even-app`):
  finite `hEven` certificate, proved modulo Lemma 5.1 and Lemma 5.10.
- `S05_Lem5_14_OddHCertificate.lean` -- Lemma 5.14 (`lem:h-odd-app`):
  finite `hOdd` certificate, proved modulo Lemma 5.2 and Lemma 5.12.

Older theorem names such as `Thm2_1_BooleanU1`, `L5_4_ZBoundApp`,
`L5_5_HEvenApp`, and `L5_6_HOddApp` are preserved inside the corresponding
`Sxx_...` files, rather than living in separate wrapper modules.

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

- `S01_Thm1_01_MainIntro.lean`: main tester statement, currently routed through the
  abstract tester-amplification interface.
- `S02_Thm2_01_BooleanU1Classification.lean`: Boolean degree-one structural input.
- `S02_Thm2_02_FKNStability.lean`: FKN/stability input.
- `S02_Lem2_03_*`: cube-character orthonormality, Fourier expansion, and
  Parseval.
- `S03_Lem3_01_DictatorToJunta.lean` and `S03_Lem3_02_PerfectCompleteness.lean`: matching
  cube completeness side.
- `S04_Lem4_01` through `S04_Lem4_13`, plus `S04_Cor4_09`,
  `S04_Thm4_10`, and `S04_Prop4_12`: matching-cube soundness reductions up to
  the one-trial soundness bound.
- `S05_Lem5_01` through `S05_Lem5_14`: current Section 5 spectral bridge and
  finite certificate files.  Older Section 5 theorem names such as
  `L5_4_ZBoundApp` are declarations inside these numbered files, not separate
  wrapper modules.

## Naming Conventions

- `S##_ThmA_BB_...`, `S##_LemA_BB_...`, `S##_PropA_BB_...`,
  `S##_CorA_BB_...`: preferred paper-facing filenames with explicit section
  and paper statement number.
- `ThmA_B_...`, `LA_B_...`, `PropA_B_...`, `CorA_B_...`: legacy
  paper-facing filenames still used by earlier sections of the scaffold.
- `Aux_...`: Lean helper lemma, implementation detail, or isolated external
  input that is not itself the paper-facing statement.

Keep theorem names stable when possible.  If a theorem is paper-numbered, keep
the declaration in the paper-numbered file even when the hard proof is factored
into an aux file.

## Development Notes

Useful commands:

```bash
lake build DictatorshipTesting
lake build DictatorshipTesting.Paper.S05_Lem5_10_ZBoundCertificate
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
