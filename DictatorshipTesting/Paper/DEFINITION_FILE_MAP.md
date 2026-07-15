# Definition File Map

Numbered paper definitions are mapped in the section files. Grouped definitions
use letter-suffixed Lean modules without creating additional paper numbers.

| Paper definition | Lean modules |
| --- | --- |
| 2.1 | `Defs/S02_Def2_01_FiniteSeedTester.lean` |
| 2.2 | `AlgebraicLibrary/BooleanCube/LowDegree.lean` |
| 4.1 | `Defs/S04_Def4_01_MatchingLocalDegreeOneAndProjection.lean` |
| 5.1--5.5 | `AlgebraicLibrary/Young/IndexedDiagram.lean`, `DiagramCorners.lean`, `StandardTableau.lean`, `TableauDimension.lean`, `OrthogonalRepresentation.lean` |
| 5.6 | `S05_Int_RegularYoungBlockDecomposition.lean` |
| 5.7 | `AlgebraicLibrary/Young/IndexedDiagram.lean`, `TableauDimension.lean` |
| 5.8--5.9 | `Defs/S05_Def5_08_SignedTwoBoxExtensionSpaces.lean`, `AlgebraicLibrary/Young/StandardTableau.lean` |
| 5.10 | `Defs/S05_Def5_10a_*`, `Defs/S05_Def5_10b_*` |
| 5.11 | `Defs/S05_Def5_11a_MatchingCharacters.lean`, `S05_Int_YoungMatchingOperators.lean` |
| 5.12 | `Defs/S05_Def5_12a_*` through `Defs/S05_Def5_12d_*` |

Library-owned definitions are listed at their defining module; no paper-side
forwarding module is retained. Files named `S##_IntDef_*` are implementation
vocabulary, not additional paper definitions.
