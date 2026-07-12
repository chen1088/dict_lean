# Paper Numbering Map

This index records the numbering used by the current compiled paper. Detailed
file mappings live in the section maps under `DictatorshipTesting/Paper/`.
Definition counters are independent from theorem-like counters. A definition
split across several Lean modules uses letter suffixes without creating extra
paper numbers.

| Section | Numbered definitions | Theorem-like statements | Detailed map |
| --- | ---: | ---: | --- |
| 1 | 0 | 1 | `DictatorshipTesting/Paper/SECTION1_FILE_MAP.md` |
| 2 | 2 | 3 | `DictatorshipTesting/Paper/SECTION2_FILE_MAP.md` |
| 3 | 0 | 2 | `DictatorshipTesting/Paper/SECTION3_FILE_MAP.md` |
| 4 | 2 | 10 | `DictatorshipTesting/Paper/SECTION4_FILE_MAP.md` |
| 5 | 12 | 26 | `DictatorshipTesting/Paper/SECTION5_FILE_MAP.md` |

Totals: 16 numbered definitions and 42 theorem-like statements.

The complete grouped-definition module map is
`DictatorshipTesting/Paper/DEFINITION_FILE_MAP.md`. Internal modules named
`SXX_Int_*`, `SXX_IntDef_*`, or `SXX_IntInst_*` do not create paper numbers.

The three representation-theory results are part of the Section 5 sequence:

| Current statement | Lean file |
| --- | --- |
| Theorem 5.3, Young orthogonal action | `S05_Thm5_03_YoungOrthogonalAction.lean` |
| Theorem 5.5, Jucys--Murphy content action | `S05_Thm5_05_JucysMurphyContentAction.lean` |
| Lemma 5.12, degree-one Young-block identification | `S05_Lem5_12_DegreeOneYoungBlockIdentification.lean` |
