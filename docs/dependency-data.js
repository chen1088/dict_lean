window.DICT_DEPENDENCY_DATA = {
  "repoUrl": "https://github.com/chen1088/dict_lean",
  "nodes": [
    {
      "id": "AppA_01",
      "label": "App A.1",
      "title": "Young orthogonal realization",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_ThmA_01_YoungOrthogonalRealization.lean",
      "wrappers": [
        "AppA_ThmA_01_youngOrthogonalRealization"
      ],
      "deps": [],
      "summary": "External marker for Young orthogonal realization.",
      "statement": "App A.1: External marker for Young orthogonal realization.",
      "terms": []
    },
    {
      "id": "AppA_02",
      "label": "App A.2",
      "title": "Jucys-Murphy content spectrum",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_ThmA_02_JucysMurphyContentSpectrum.lean",
      "wrappers": [
        "AppA_ThmA_02_jucysMurphyContentSpectrum"
      ],
      "deps": [],
      "summary": "External marker for the Jucys-Murphy content spectrum.",
      "statement": "App A.2: External marker for the Jucys-Murphy content spectrum.",
      "terms": []
    },
    {
      "id": "AppA_03",
      "label": "App A.3",
      "title": "Degree-one Young-block identification",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_LemA_03_DegreeOneYoungBlockIdentification.lean",
      "wrappers": [
        "AppA_LemA_03_degreeOneYoungBlockIdentification"
      ],
      "deps": [],
      "summary": "External marker identifying the degree-one Young blocks.",
      "statement": "App A.3: External marker identifying the degree-one Young blocks.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ]
    },
    {
      "id": "AppA_04",
      "label": "App A.4",
      "title": "Standard tableaux connectedness",
      "section": "Appendix A",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/AppA_LemA_04_StandardTableauxSwapConnectedness.lean",
      "wrappers": [
        "AppA_LemA_04_standardTableauxSwapConnectedness"
      ],
      "deps": [],
      "summary": "External marker for connectedness under adjacent swaps.",
      "statement": "App A.4: External marker for connectedness under adjacent swaps.",
      "terms": [
        {
          "text": "standard tableaux",
          "target": "S05_D03"
        }
      ]
    },
    {
      "id": "AuxSpectralBridge",
      "label": "Aux",
      "title": "Spectral bridge algebra",
      "section": "Auxiliary layer",
      "kind": "aux",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Aux_SpectralBridgeDimensionParam.lean",
      "wrappers": [
        "SpectralGapFromBlockModelWithDim"
      ],
      "deps": [
        "S05_L16",
        "S05_L17"
      ],
      "summary": "Dimension-parameterized algebra behind the spectral bridge.",
      "statement": "Aux: Dimension-parameterized algebra behind the spectral bridge.",
      "terms": [
        {
          "text": "Block scalar of averaged rejection",
          "target": "S05_L16"
        },
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L17"
        },
        {
          "text": "block scalar",
          "target": "S05_L16"
        },
        {
          "text": "block lower bound",
          "target": "S05_L17"
        }
      ]
    },
    {
      "id": "AuxStandardYoungTableaux",
      "label": "Aux",
      "title": "Standard-tableau deletion API",
      "section": "Auxiliary layer",
      "kind": "aux",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Aux_StandardYoungTableaux.lean",
      "wrappers": [
        "deleteMax",
        "insertMax"
      ],
      "deps": [
        "S05_D01",
        "S05_D02"
      ],
      "summary": "Concrete standard-tableau deletion, insertion, and child equivalence API.",
      "statement": "Aux: Concrete standard-tableau deletion, insertion, and child equivalence API.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        },
        {
          "text": "Young diagrams",
          "target": "S05_D01"
        },
        {
          "text": "removable corners",
          "target": "S05_D02"
        }
      ]
    },
    {
      "id": "AuxTableauDimension",
      "label": "Aux",
      "title": "Tableau dimension counting",
      "section": "Auxiliary layer",
      "kind": "aux",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Aux_TableauDimension.lean",
      "wrappers": [
        "tableauDim"
      ],
      "deps": [
        "S05_D03"
      ],
      "summary": "Finite tableau-count dimension helpers.",
      "statement": "Aux: Finite tableau-count dimension helpers.",
      "terms": [
        {
          "text": "Standard tableaux and occupation",
          "target": "S05_D03"
        },
        {
          "text": "standard tableaux",
          "target": "S05_D03"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        }
      ]
    },
    {
      "id": "AuxYoungMatchingOperators",
      "label": "Aux",
      "title": "Matching operators",
      "section": "Auxiliary layer",
      "kind": "aux",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Aux_YoungMatchingOperators.lean",
      "wrappers": [
        "canonicalMatchingYoungOperatorEven",
        "matchingSignProjectionEven"
      ],
      "deps": [
        "S05_L01"
      ],
      "summary": "Canonical matching-edge operators and simultaneous sign projections.",
      "statement": "Aux: Canonical matching-edge operators and simultaneous sign projections.",
      "terms": [
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "matching eigenvectors",
          "target": "S05_D16"
        }
      ]
    },
    {
      "id": "AuxYoungOrthogonal",
      "label": "Aux",
      "title": "Young adjacent operators",
      "section": "Auxiliary layer",
      "kind": "aux",
      "importance": "minor",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/Aux_YoungOrthogonal.lean",
      "wrappers": [
        "youngAdjacentOperator"
      ],
      "deps": [
        "S05_D03",
        "S05_D04"
      ],
      "summary": "Concrete Young-basis adjacent operators and coefficients.",
      "statement": "Aux: Concrete Young-basis adjacent operators and coefficients.",
      "terms": [
        {
          "text": "Standard tableaux and occupation",
          "target": "S05_D03"
        },
        {
          "text": "Tableau coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "tableau coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "Young adjacent operators",
          "target": "S05_D05"
        }
      ]
    },
    {
      "id": "L2_3",
      "label": "Lem 2.3",
      "title": "Cube Fourier facts",
      "section": "Section 2",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S02_Lem2_03_CubeParseval.lean",
      "wrappers": [
        "L2_3_CubeParseval"
      ],
      "deps": [],
      "summary": "Cube-character orthonormality, Fourier expansion, and Parseval wrappers.",
      "statement": "Lem 2.3: Cube-character orthonormality, Fourier expansion, and Parseval wrappers.",
      "terms": []
    },
    {
      "id": "L4_1",
      "label": "Lem 4.1",
      "title": "Cube square test",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_01_CubeSquare.lean",
      "wrappers": [
        "L4_1_CubeSquare"
      ],
      "deps": [
        "L2_3"
      ],
      "summary": "Boolean-cube square test Fourier calculation.",
      "statement": "Lem 4.1: Boolean-cube square test Fourier calculation.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ]
    },
    {
      "id": "L4_11",
      "label": "Lem 4.11",
      "title": "Trial cube coordinates",
      "section": "Section 4",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_11_TrialCubeCoordinates.lean",
      "wrappers": [
        "L4_11_TrialCubeCoordinates"
      ],
      "deps": [
        "L4_1"
      ],
      "summary": "Identifies a group trial with a Boolean-cube square test on a matching coset.",
      "statement": "Lem 4.11: Identifies a group trial with a Boolean-cube square test on a matching coset.",
      "terms": [
        {
          "text": "Cube square test",
          "target": "L4_1"
        }
      ]
    },
    {
      "id": "L4_13",
      "label": "Lem 4.13",
      "title": "One-trial soundness",
      "section": "Main spine",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Lem4_13_OneTrialSoundness.lean",
      "wrappers": [
        "L4_13_OneTrialSoundness"
      ],
      "deps": [
        "Thm2_2",
        "Prop4_12"
      ],
      "summary": "Combines square-energy control with the FKN input.",
      "statement": "Lem 4.13: Combines square-energy control with the FKN input.",
      "terms": [
        {
          "text": "FKN/stability input",
          "target": "Thm2_2"
        },
        {
          "text": "Square energy controls global degree",
          "target": "Prop4_12"
        }
      ]
    },
    {
      "id": "Prop4_12",
      "label": "Prop 4.12",
      "title": "Square energy controls global degree",
      "section": "Main spine",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Prop4_12_SquareEnergyControlsGlobalDegree.lean",
      "wrappers": [
        "Prop4_12_SquareEnergyControlsGlobalDegree"
      ],
      "deps": [
        "L4_11",
        "Thm4_10"
      ],
      "summary": "Uses the matching spectral gap to control distance from U1.",
      "statement": "Prop 4.12: Uses the matching spectral gap to control distance from U1.",
      "terms": [
        {
          "text": "Trial cube coordinates",
          "target": "L4_11"
        },
        {
          "text": "Matching-cube spectral gap",
          "target": "Thm4_10"
        },
        {
          "text": "U1",
          "target": "S05_D08"
        }
      ]
    },
    {
      "id": "S05_D01",
      "label": "Def 5.1",
      "title": "Young diagrams and boxes",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_01_YoungDiagramsAndBoxes.lean",
      "wrappers": [
        "S05_Def5_01_YoungDiagram",
        "S05_Def5_01_youngRow",
        "S05_Def5_01_youngCells"
      ],
      "deps": [],
      "summary": "Young diagrams, row lengths, boxes, and cells.",
      "statement": "Definition 5.1 introduces Young diagrams, row lengths, Young cells, and the finite set of boxes used throughout the tableau proof.",
      "terms": []
    },
    {
      "id": "S05_D02",
      "label": "Def 5.2",
      "title": "Removable corners and one-box removals",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_02_RemovableCorners.lean",
      "wrappers": [
        "S05_Def5_02_IsYoungSubdiagram",
        "S05_Def5_02_IsOneBoxChild",
        "S05_Def5_02_oneBoxChildren",
        "S05_Def5_02_IsRemovableRow"
      ],
      "deps": [
        "S05_D01"
      ],
      "summary": "Subdiagrams, removable rows/corners, one-box children, and finite one-box child sets.",
      "statement": "Definition 5.2 introduces Young subdiagrams, one-box children, removable rows, and removable corners.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "one-box removals",
          "target": "S05_D11"
        }
      ]
    },
    {
      "id": "S05_D03",
      "label": "Def 5.3",
      "title": "Standard tableaux and occupation",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_03_StandardTableaux.lean",
      "wrappers": [
        "S05_Def5_03_StandardYoungTableau",
        "S05_Def5_03_cellOfEntry",
        "S05_Def5_03_TableauMaxAt"
      ],
      "deps": [
        "S05_D01",
        "AuxStandardYoungTableaux"
      ],
      "summary": "Standard Young tableaux and the cell occupied by an entry.",
      "statement": "Definition 5.3 introduces standard Young tableaux, the occupied cell of an entry, and the maximum-entry-at-a-cell predicate.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        },
        {
          "text": "Standard-tableau deletion API",
          "target": "AuxStandardYoungTableaux"
        }
      ]
    },
    {
      "id": "S05_D04",
      "label": "Def 5.4",
      "title": "Tableau coordinate space",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_04_TableauCoordinateSpace.lean",
      "wrappers": [
        "S05_Def5_04_tableauDim",
        "S05_Def5_04_TableauSpace",
        "S05_Def5_04_tableauBasisVec"
      ],
      "deps": [
        "S05_D03",
        "AuxTableauDimension",
        "AuxYoungOrthogonal"
      ],
      "summary": "Tableau-count dimension, coordinate space, and Young basis vectors.",
      "statement": "Definition 5.4 introduces tableauDim, the tableau coordinate space, and basis vectors indexed by standard tableaux.",
      "terms": [
        {
          "text": "Standard tableaux and occupation",
          "target": "S05_D03"
        },
        {
          "text": "Tableau dimension counting",
          "target": "AuxTableauDimension"
        },
        {
          "text": "Young adjacent operators",
          "target": "AuxYoungOrthogonal"
        },
        {
          "text": "standard tableaux",
          "target": "S05_D03"
        }
      ]
    },
    {
      "id": "S05_D05",
      "label": "Def 5.5",
      "title": "Contents and adjacent operators",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_05_ContentAndAdjacentOperators.lean",
      "wrappers": [
        "S05_Def5_05_cellContent",
        "S05_Def5_05_entryContent",
        "S05_Def5_05_youngAdjacentOperator",
        "S05_Def5_05_diagonalContentOperator"
      ],
      "deps": [
        "S05_D04"
      ],
      "summary": "Contents, adjacent transposition operators, and diagonal content operators.",
      "statement": "Definition 5.5 introduces cell content, entry content, Young adjacent operators, and diagonal content operators.",
      "terms": [
        {
          "text": "Tableau coordinate space",
          "target": "S05_D04"
        }
      ]
    },
    {
      "id": "S05_D06",
      "label": "Def 5.6",
      "title": "Young block",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_06_YoungBlock.lean",
      "wrappers": [
        "S05_YoungBlock"
      ],
      "deps": [
        "S05_D01"
      ],
      "summary": "Young-block index vocabulary.",
      "statement": "Definition 5.6 introduces the Young block indices used in the spectral decomposition interface.",
      "terms": [
        {
          "text": "Young diagrams and boxes",
          "target": "S05_D01"
        }
      ]
    },
    {
      "id": "S05_D07",
      "label": "Def 5.7",
      "title": "Young-block energy profile",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_07_YoungBlockEnergyProfile.lean",
      "wrappers": [
        "S05_Def5_07_YoungBlockEnergyProfile"
      ],
      "deps": [
        "S05_D06"
      ],
      "summary": "Nonnegative Young-block energy profile interface.",
      "statement": "Definition 5.7 introduces the nonnegative Young-block energy profile.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ]
    },
    {
      "id": "S05_D08",
      "label": "Def 5.8",
      "title": "U1-compatible block profile",
      "section": "Definitions",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_08_U1CompatibleYoungBlockProfile.lean",
      "wrappers": [
        "S05_Def5_08_U1CompatibleYoungBlockProfile"
      ],
      "deps": [
        "S05_D07"
      ],
      "summary": "Numerical identification of the one-row and standard blocks with U1.",
      "statement": "Definition 5.8 introduces the U1-compatible Young-block profile identifying the one-row and standard blocks with U1.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D07"
        }
      ]
    },
    {
      "id": "S05_D09",
      "label": "Def 5.9",
      "title": "Two-box removals",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_09_TwoBoxRemovals.lean",
      "wrappers": [
        "S05_IsHorizontalTwoBoxRemoval",
        "S05_IsVerticalTwoBoxRemoval"
      ],
      "deps": [
        "S05_D02"
      ],
      "summary": "Horizontal and vertical two-box removal predicates.",
      "statement": "Definition 5.9 introduces horizontal and vertical two-box removals.",
      "terms": [
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        }
      ]
    },
    {
      "id": "S05_D10",
      "label": "Def 5.10",
      "title": "Signed two-box removals",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_10_SignedTwoBoxRemovals.lean",
      "wrappers": [
        "S05_PositiveSignedTwoBoxRemoval",
        "S05_NegativeSignedTwoBoxRemoval"
      ],
      "deps": [
        "S05_D09"
      ],
      "summary": "Signs attached to horizontal and vertical two-box removals.",
      "statement": "Definition 5.10 introduces signed two-box removals.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        },
        {
          "text": "two-box removals",
          "target": "S05_D09"
        }
      ]
    },
    {
      "id": "S05_D11",
      "label": "Def 5.11",
      "title": "One-box removals",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_11_OneBoxRemovals.lean",
      "wrappers": [
        "S05_IsOneBoxRemoval",
        "S05_oneBoxChildrenOdd"
      ],
      "deps": [
        "S05_D02"
      ],
      "summary": "One-box removal vocabulary.",
      "statement": "Definition 5.11 introduces one-box removals and odd one-box children.",
      "terms": [
        {
          "text": "Removable corners and one-box removals",
          "target": "S05_D02"
        },
        {
          "text": "one-box children",
          "target": "S05_D02"
        }
      ]
    },
    {
      "id": "S05_D12",
      "label": "Def 5.12",
      "title": "One-box deletion spaces",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_12_OneBoxDeletionSpaces.lean",
      "wrappers": [
        "S05_Def5_12_OneBoxDeletionTableaux"
      ],
      "deps": [
        "S05_D11"
      ],
      "summary": "Deletion-fiber coordinate-space vocabulary.",
      "statement": "Definition 5.12 introduces the one-box deletion coordinate spaces.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D11"
        },
        {
          "text": "coordinate space",
          "target": "S05_D04"
        },
        {
          "text": "one-box deletion",
          "target": "S05_L05"
        }
      ]
    },
    {
      "id": "S05_D13",
      "label": "Def 5.13",
      "title": "Even sign-pattern multiset",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_13_EvenSignPatternMultiset.lean",
      "wrappers": [
        "S05_evenZeroSignPatternCount",
        "S05_evenHighSignPatternCount"
      ],
      "deps": [
        "S05_D09"
      ],
      "summary": "Even zero/high sign-pattern counters.",
      "statement": "Definition 5.13 introduces the even sign-pattern multiset counters.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        }
      ]
    },
    {
      "id": "S05_D14",
      "label": "Def 5.14",
      "title": "Odd sign-pattern multiset",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_14_OddSignPatternMultiset.lean",
      "wrappers": [
        "S05_oddHighSignPatternCount"
      ],
      "deps": [
        "S05_D11"
      ],
      "summary": "Odd high sign-pattern counter.",
      "statement": "Definition 5.14 introduces the odd sign-pattern multiset counter.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D11"
        }
      ]
    },
    {
      "id": "S05_D15",
      "label": "Def 5.15",
      "title": "Matching characters",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_15_MatchingCharacters.lean",
      "wrappers": [
        "S05_matchingCharacter",
        "S05_matchingCharacterWeight"
      ],
      "deps": [
        "L2_3"
      ],
      "summary": "Matching-cube character vocabulary.",
      "statement": "Definition 5.15 introduces matching characters and their weights on matching cubes.",
      "terms": [
        {
          "text": "Cube Fourier facts",
          "target": "L2_3"
        }
      ]
    },
    {
      "id": "S05_D16",
      "label": "Def 5.16",
      "title": "Even matching eigenvectors",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_16_IsMatchingEigenvectorEven.lean",
      "wrappers": [
        "S05_IsMatchingEigenvectorEven"
      ],
      "deps": [
        "AuxYoungMatchingOperators"
      ],
      "summary": "Even simultaneous matching-edge eigenvector predicate.",
      "statement": "Definition 5.16 introduces the even simultaneous matching-eigenvector predicate.",
      "terms": [
        {
          "text": "Matching operators",
          "target": "AuxYoungMatchingOperators"
        }
      ]
    },
    {
      "id": "S05_D17",
      "label": "Def 5.17",
      "title": "Odd matching eigenvectors",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_17_IsMatchingEigenvectorOdd.lean",
      "wrappers": [
        "S05_IsMatchingEigenvectorOdd"
      ],
      "deps": [
        "AuxYoungMatchingOperators"
      ],
      "summary": "Odd simultaneous matching-edge eigenvector predicate.",
      "statement": "Definition 5.17 introduces the odd simultaneous matching-eigenvector predicate.",
      "terms": [
        {
          "text": "Matching operators",
          "target": "AuxYoungMatchingOperators"
        }
      ]
    },
    {
      "id": "S05_D18",
      "label": "Def 5.18",
      "title": "Even restriction scalar input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_18_MatchingRestrictionEvenInput.lean",
      "wrappers": [
        "MatchingRestrictionEvenInput"
      ],
      "deps": [
        "S05_D13"
      ],
      "summary": "Even scalar matching-restriction input.",
      "statement": "Definition 5.18 introduces the even matching-restriction scalar input.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        }
      ]
    },
    {
      "id": "S05_D19",
      "label": "Def 5.19",
      "title": "Odd restriction scalar input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_19_MatchingRestrictionOddInput.lean",
      "wrappers": [
        "MatchingRestrictionOddInput"
      ],
      "deps": [
        "S05_D14"
      ],
      "summary": "Odd scalar matching-restriction input.",
      "statement": "Definition 5.19 introduces the odd matching-restriction scalar input.",
      "terms": [
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        },
        {
          "text": "matching-restriction scalar input",
          "target": "S05_D18"
        }
      ]
    },
    {
      "id": "S05_D20",
      "label": "Def 5.20",
      "title": "Even trace input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_20_TraceLocalTruncationEvenInput.lean",
      "wrappers": [
        "TraceLocalTruncationEvenInput"
      ],
      "deps": [
        "S05_D18"
      ],
      "summary": "Even scalar trace formula interface.",
      "statement": "Definition 5.20 introduces the even local-truncation trace input.",
      "terms": [
        {
          "text": "Even restriction scalar input",
          "target": "S05_D18"
        }
      ]
    },
    {
      "id": "S05_D21",
      "label": "Def 5.21",
      "title": "Odd trace input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_21_TraceLocalTruncationOddInput.lean",
      "wrappers": [
        "TraceLocalTruncationOddInput"
      ],
      "deps": [
        "S05_D19"
      ],
      "summary": "Odd scalar trace formula interface.",
      "statement": "Definition 5.21 introduces the odd local-truncation trace input.",
      "terms": [
        {
          "text": "Odd restriction scalar input",
          "target": "S05_D19"
        },
        {
          "text": "local-truncation trace input",
          "target": "S05_D20"
        }
      ]
    },
    {
      "id": "S05_D22",
      "label": "Def 5.22",
      "title": "Matching idempotents",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Def5_22_MatchingIdempotents.lean",
      "wrappers": [
        "S05_matchingLowIdempotent",
        "S05_matchingHighIdempotent",
        "S05_matchingLow_add_matchingHigh"
      ],
      "deps": [
        "S05_D15"
      ],
      "summary": "Low/high matching idempotents and their complementary identities.",
      "statement": "Definition 5.22 introduces the low and high matching idempotents and proves their complementary identities.",
      "terms": [
        {
          "text": "Matching characters",
          "target": "S05_D15"
        }
      ]
    },
    {
      "id": "S05_D23",
      "label": "Def 5.23",
      "title": "Young-basis scalar commutant input",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "interface",
      "file": "DictatorshipTesting/Paper/S05_Def5_23_YoungBasisScalarCommutantInput.lean",
      "wrappers": [
        "S05_Def5_23_YoungBasisScalarCommutantInput"
      ],
      "deps": [
        "S05_D06"
      ],
      "summary": "Scalarity interface consumed by the spectral bridge.",
      "statement": "Definition 5.23 introduces the Young-basis scalar commutant input.",
      "terms": [
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ]
    },
    {
      "id": "S05_L01",
      "label": "Lem 5.1",
      "title": "Tableau Coxeter model",
      "section": "Tableau operators",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean",
      "wrappers": [
        "S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel"
      ],
      "deps": [
        "S05_D05",
        "AuxYoungOrthogonal"
      ],
      "summary": "Concrete adjacent-transposition matrices on tableau coordinates.",
      "statement": "Lemma 5.1 proves the concrete tableau-coordinate Coxeter model for adjacent transpositions.",
      "terms": [
        {
          "text": "Contents and adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "Young adjacent operators",
          "target": "AuxYoungOrthogonal"
        }
      ]
    },
    {
      "id": "S05_L02",
      "label": "Lem 5.2",
      "title": "Diagonal content eigenspaces",
      "section": "Tableau operators",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_02_DiagonalContentEigenspaces.lean",
      "wrappers": [
        "S05_Lem5_02_diagonalContentEigenspaces"
      ],
      "deps": [
        "S05_D05",
        "AppA_02"
      ],
      "summary": "Explicit diagonal content eigenspaces in the tableau basis.",
      "statement": "Lemma 5.2 proves diagonal content eigenspaces for the explicit content operators.",
      "terms": [
        {
          "text": "Contents and adjacent operators",
          "target": "S05_D05"
        },
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "AppA_02"
        }
      ]
    },
    {
      "id": "S05_L03",
      "label": "Lem 5.3",
      "title": "Two-box tableau branching",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_03_TwoBoxTableauBranching.lean",
      "wrappers": [
        "S05_Lem5_03_twoStepDeletionTableauxEquivChildTableaux"
      ],
      "deps": [
        "S05_D09",
        "AuxStandardYoungTableaux"
      ],
      "summary": "Fixed two-step deletion equivalence for tableaux.",
      "statement": "Lemma 5.3 proves fixed two-box tableau branching by iterated maximum-entry deletion.",
      "terms": [
        {
          "text": "Two-box removals",
          "target": "S05_D09"
        },
        {
          "text": "Standard-tableau deletion API",
          "target": "AuxStandardYoungTableaux"
        }
      ]
    },
    {
      "id": "S05_L04",
      "label": "Lem 5.4",
      "title": "One-box corner decomposition",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_04_OneBoxCornerDecomposition.lean",
      "wrappers": [
        "S05_Lem5_04_row_form",
        "S05_Lem5_04_removable_corner"
      ],
      "deps": [
        "S05_D11"
      ],
      "summary": "A one-box child removes a unique removable corner.",
      "statement": "Lemma 5.4 proves that one-box children differ in a unique removable corner.",
      "terms": [
        {
          "text": "One-box removals",
          "target": "S05_D11"
        },
        {
          "text": "one-box children",
          "target": "S05_D02"
        }
      ]
    },
    {
      "id": "S05_L05",
      "label": "Lem 5.5",
      "title": "One-box deletion is unitary",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_05_OneBoxDeletionIsUnitary.lean",
      "wrappers": [
        "S05_Lem5_05_deletionCoordinateMap_inner"
      ],
      "deps": [
        "S05_D12",
        "S05_L04"
      ],
      "summary": "The deletion coordinate map preserves the finite coordinate inner product.",
      "statement": "Lemma 5.5 proves that one-box deletion is unitary on the finite coordinate spaces.",
      "terms": [
        {
          "text": "One-box deletion spaces",
          "target": "S05_D12"
        },
        {
          "text": "One-box corner decomposition",
          "target": "S05_L04"
        },
        {
          "text": "coordinate space",
          "target": "S05_D04"
        }
      ]
    },
    {
      "id": "S05_L06",
      "label": "Lem 5.6",
      "title": "Deletion intertwines earlier swaps",
      "section": "Finite tableau data",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_06_OneBoxDeletionIntertwinesEarlierSwaps.lean",
      "wrappers": [
        "S05_Lem5_06_deletionCoordinateMap_youngAdjacentOperator_intertwines"
      ],
      "deps": [
        "S05_L05",
        "S05_L01"
      ],
      "summary": "One-box deletion intertwines earlier adjacent operators and content operators.",
      "statement": "Lemma 5.6 proves that one-box deletion intertwines earlier adjacent swaps and content operators.",
      "terms": [
        {
          "text": "One-box deletion is unitary",
          "target": "S05_L05"
        },
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "one-box deletion",
          "target": "S05_L05"
        }
      ]
    },
    {
      "id": "S05_L07",
      "label": "Lem 5.7",
      "title": "Two-box dimension recursion",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_07_TwoBoxDimensionRecursion.lean",
      "wrappers": [
        "S05_Lem5_07_tableauDim_twoStrip_branching_sized"
      ],
      "deps": [
        "S05_L03"
      ],
      "summary": "Tableau-count dimension recursion for two-box removals.",
      "statement": "Lemma 5.7 proves the two-box tableauDim dimension recursion.",
      "terms": [
        {
          "text": "Two-box tableau branching",
          "target": "S05_L03"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "two-box removals",
          "target": "S05_D09"
        }
      ]
    },
    {
      "id": "S05_L08",
      "label": "Lem 5.8",
      "title": "One-box dimension recursion",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_08_OneBoxDimensionRecursion.lean",
      "wrappers": [
        "S05_Lem5_08_tableauDim_oneBoxChildrenOdd_branching"
      ],
      "deps": [
        "S05_L05"
      ],
      "summary": "Tableau-count dimension recursion for one-box removals.",
      "statement": "Lemma 5.8 proves the one-box tableauDim dimension recursion.",
      "terms": [
        {
          "text": "One-box deletion is unitary",
          "target": "S05_L05"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        },
        {
          "text": "one-box removals",
          "target": "S05_D11"
        }
      ]
    },
    {
      "id": "S05_L09",
      "label": "Lem 5.9",
      "title": "Sizes of sign-pattern multisets",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_09_SizesOfTheSignPatternMultisets.lean",
      "wrappers": [
        "S05_Lem5_09_tableauDim_twoStrip_size",
        "S05_Lem5_09_tableauDim_oneBox_size"
      ],
      "deps": [
        "S05_D13",
        "S05_D14",
        "S05_L07",
        "S05_L08"
      ],
      "summary": "Tableau-count size identities for sign-pattern multisets.",
      "statement": "Lemma 5.9 proves the size identities for the sign-pattern multisets.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        },
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L07"
        },
        {
          "text": "One-box dimension recursion",
          "target": "S05_L08"
        }
      ]
    },
    {
      "id": "S05_L10",
      "label": "Lem 5.10",
      "title": "Matching subgroup eigenbasis",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_10_MatchingSubgroupEigenbasis.lean",
      "wrappers": [
        "S05_Lem5_10_matchingSignProjectionEven_isMatchingEigenvector",
        "S05_Lem5_10_matchingSignProjectionOdd_isMatchingEigenvector"
      ],
      "deps": [
        "S05_L01",
        "S05_D15",
        "S05_D16",
        "S05_D17",
        "S05_D18",
        "S05_D19",
        "AuxYoungMatchingOperators"
      ],
      "summary": "Concrete matching-operator and sign-projection wrappers.",
      "statement": "Lemma 5.10 proves the concrete matching-subgroup eigenbasis and sign-projection wrappers.",
      "terms": [
        {
          "text": "Tableau Coxeter model",
          "target": "S05_L01"
        },
        {
          "text": "Matching characters",
          "target": "S05_D15"
        },
        {
          "text": "Even matching eigenvectors",
          "target": "S05_D16"
        },
        {
          "text": "Odd matching eigenvectors",
          "target": "S05_D17"
        },
        {
          "text": "Even restriction scalar input",
          "target": "S05_D18"
        },
        {
          "text": "Odd restriction scalar input",
          "target": "S05_D19"
        },
        {
          "text": "Matching operators",
          "target": "AuxYoungMatchingOperators"
        }
      ]
    },
    {
      "id": "S05_L11",
      "label": "Lem 5.11",
      "title": "Local truncation on a matching character",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_11_LocalTruncationOnAMatchingCharacter.lean",
      "wrappers": [
        "S05_Lem5_11_matchingLocalProjection_preserves_low_matchingCharacter",
        "S05_Lem5_11_matchingLocalProjection_kills_high_matchingCharacter"
      ],
      "deps": [
        "S05_D15"
      ],
      "summary": "Matching-character local truncation calculation.",
      "statement": "Lemma 5.11 proves local truncation on a matching character.",
      "terms": [
        {
          "text": "Matching characters",
          "target": "S05_D15"
        }
      ]
    },
    {
      "id": "S05_L12",
      "label": "Lem 5.12",
      "title": "Trace of one local truncation",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock.lean",
      "wrappers": [
        "traceLocalTruncation_even_from_restriction",
        "traceLocalTruncation_odd_from_restriction"
      ],
      "deps": [
        "S05_L10",
        "S05_L11",
        "S05_D20",
        "S05_D21"
      ],
      "summary": "Trace formula wrappers from explicit scalar inputs; the block trace model is representation input.",
      "statement": "Lemma 5.12 states the trace of one local truncation on one Young block from explicit scalar inputs.",
      "terms": [
        {
          "text": "Matching subgroup eigenbasis",
          "target": "S05_L10"
        },
        {
          "text": "Local truncation on a matching character",
          "target": "S05_L11"
        },
        {
          "text": "Even trace input",
          "target": "S05_D20"
        },
        {
          "text": "Odd trace input",
          "target": "S05_D21"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        }
      ]
    },
    {
      "id": "S05_L13",
      "label": "Lem 5.13",
      "title": "Local truncation as convolution",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_13_LocalTruncationAsConvolution.lean",
      "wrappers": [
        "S05_Lem5_13_local_truncation_as_convolution"
      ],
      "deps": [
        "S05_L11",
        "S05_D22"
      ],
      "summary": "Local projection as low convolution and residual as high convolution.",
      "statement": "Lemma 5.13 proves local truncation as low/high convolution.",
      "terms": [
        {
          "text": "Local truncation on a matching character",
          "target": "S05_L11"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D22"
        }
      ]
    },
    {
      "id": "S05_L14",
      "label": "Lem 5.14",
      "title": "Central averaged rejection",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_14_CentralAveragedRejection.lean",
      "wrappers": [
        "S05_Lem5_14_matchingMeanProjectionError_eq_high_idempotent_average"
      ],
      "deps": [
        "S05_L13",
        "S05_D22"
      ],
      "summary": "Finite-average identity is proved; centrality on Young blocks is representation input.",
      "statement": "Lemma 5.14 proves the finite averaged-rejection identity, with centrality supplied by the spectral model boundary.",
      "terms": [
        {
          "text": "Local truncation as convolution",
          "target": "S05_L13"
        },
        {
          "text": "Matching idempotents",
          "target": "S05_D22"
        },
        {
          "text": "Young block",
          "target": "S05_D06"
        },
        {
          "text": "spectral model",
          "target": "S05_L18"
        }
      ]
    },
    {
      "id": "S05_L15",
      "label": "Lem 5.15",
      "title": "Young-basis scalar commutant",
      "section": "Matching algebra",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_15_YoungBasisScalarCommutant.lean",
      "wrappers": [
        "S05_Lem5_15_matchingAverageScalarity_eq_sum"
      ],
      "deps": [
        "S05_L14",
        "S05_D23",
        "AppA_04"
      ],
      "summary": "Projection from scalarity input to the weighted-sum identity.",
      "statement": "Lemma 5.15 derives the Young-basis scalar commutant identity from the scalarity input.",
      "terms": [
        {
          "text": "Central averaged rejection",
          "target": "S05_L14"
        },
        {
          "text": "Young-basis scalar commutant input",
          "target": "S05_D23"
        },
        {
          "text": "Standard tableaux connectedness",
          "target": "AppA_04"
        },
        {
          "text": "scalar commutant",
          "target": "S05_D23"
        }
      ]
    },
    {
      "id": "S05_L16",
      "label": "Lem 5.16",
      "title": "Block scalar of averaged rejection",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S05_Lem5_16_BlockScalarOfTheAveragedRejection.lean",
      "wrappers": [
        "S05_Lem5_16_scalar_eq_trace_div_dimension",
        "S05_Lem5_16_even_scalar_eq_hEven_div_dim"
      ],
      "deps": [
        "S05_L12",
        "S05_L15"
      ],
      "summary": "Trace-divided-by-dimension algebra from explicit scalarity and trace identities.",
      "statement": "Lemma 5.16 derives the block scalar of the averaged rejection from trace and scalar inputs.",
      "terms": [
        {
          "text": "Trace of one local truncation",
          "target": "S05_L12"
        },
        {
          "text": "Young-basis scalar commutant",
          "target": "S05_L15"
        }
      ]
    },
    {
      "id": "S05_L17",
      "label": "Lem 5.17",
      "title": "Block lower bound implies the gap",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_17_BlockLowerBoundImpliesTheGap.lean",
      "wrappers": [
        "S05_Lem5_17_spectralGapFromBlockModelWithDim"
      ],
      "deps": [
        "S05_D07",
        "S05_D08",
        "S05_L16",
        "AuxSpectralBridge"
      ],
      "summary": "Weighted-sum spectral-gap algebra from block scalar lower bounds.",
      "statement": "Lemma 5.17 proves that a block lower bound implies the global spectral gap.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D07"
        },
        {
          "text": "U1-compatible block profile",
          "target": "S05_D08"
        },
        {
          "text": "Block scalar of averaged rejection",
          "target": "S05_L16"
        },
        {
          "text": "Spectral bridge algebra",
          "target": "AuxSpectralBridge"
        }
      ]
    },
    {
      "id": "S05_L18",
      "label": "Lem 5.18",
      "title": "Regular Young-block decomposition",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_18_RegularYoungBlockDecomposition.lean",
      "wrappers": [
        "spectralBlockModelInputWithDim_even_from_appendixA",
        "spectralBlockModelInputWithDim_odd_from_appendixA"
      ],
      "deps": [
        "S05_D07",
        "S05_D08",
        "AppA_01",
        "AppA_02",
        "AppA_03",
        "AppA_04"
      ],
      "summary": "Assembles Appendix A markers into the dimension-parameterized spectral-block model.",
      "statement": "Lemma 5.18 assembles Appendix A ingredients into the regular Young-block spectral model.",
      "terms": [
        {
          "text": "Young-block energy profile",
          "target": "S05_D07"
        },
        {
          "text": "U1-compatible block profile",
          "target": "S05_D08"
        },
        {
          "text": "Young orthogonal realization",
          "target": "AppA_01"
        },
        {
          "text": "Jucys-Murphy content spectrum",
          "target": "AppA_02"
        },
        {
          "text": "Degree-one Young-block identification",
          "target": "AppA_03"
        },
        {
          "text": "Standard tableaux connectedness",
          "target": "AppA_04"
        }
      ]
    },
    {
      "id": "S05_L19",
      "label": "Lem 5.19",
      "title": "Even spectral bridge",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_19_EvenSpectralBridge.lean",
      "wrappers": [
        "S05_Lem5_19_tableauDim_evenSpectralGapFromCertificates"
      ],
      "deps": [
        "S05_L17",
        "S05_L18",
        "S05_L24"
      ],
      "summary": "Even algebraic bridge from spectral model plus finite certificate.",
      "statement": "Lemma 5.19 proves the even spectral bridge from the spectral model and finite even certificate.",
      "terms": [
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L17"
        },
        {
          "text": "Regular Young-block decomposition",
          "target": "S05_L18"
        },
        {
          "text": "Even certificate",
          "target": "S05_L24"
        },
        {
          "text": "spectral model",
          "target": "S05_L18"
        }
      ]
    },
    {
      "id": "S05_L20",
      "label": "Lem 5.20",
      "title": "Odd spectral bridge",
      "section": "Spectral bridge",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_20_OddSpectralBridge.lean",
      "wrappers": [
        "S05_Lem5_20_tableauDim_oddSpectralGapFromCertificates"
      ],
      "deps": [
        "S05_L17",
        "S05_L18",
        "S05_L26"
      ],
      "summary": "Odd algebraic bridge from spectral model plus finite certificate.",
      "statement": "Lemma 5.20 proves the odd spectral bridge from the spectral model and finite odd certificate.",
      "terms": [
        {
          "text": "Block lower bound implies the gap",
          "target": "S05_L17"
        },
        {
          "text": "Regular Young-block decomposition",
          "target": "S05_L18"
        },
        {
          "text": "Odd certificate",
          "target": "S05_L26"
        },
        {
          "text": "spectral model",
          "target": "S05_L18"
        }
      ]
    },
    {
      "id": "S05_L21",
      "label": "Lem 5.21",
      "title": "Counting one more matching edge",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_21_CountingOneMoreMatchingEdge.lean",
      "wrappers": [
        "S05_Lem5_21_counting_one_more_matching_edge"
      ],
      "deps": [
        "S05_D13",
        "S05_D14"
      ],
      "summary": "Finite recurrence for zero/high sign-pattern counts.",
      "statement": "Lemma 5.21 proves the counting-one-more-matching-edge recurrence.",
      "terms": [
        {
          "text": "Even sign-pattern multiset",
          "target": "S05_D13"
        },
        {
          "text": "Odd sign-pattern multiset",
          "target": "S05_D14"
        }
      ]
    },
    {
      "id": "S05_L22",
      "label": "Lem 5.22",
      "title": "Weight-zero entries are never a majority",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "major",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_22_WeightZeroEntriesAreNeverAMajority.lean",
      "wrappers": [
        "S05_Lem5_22_tableau_weightZeroEntries_never_majority"
      ],
      "deps": [
        "S05_L07",
        "S05_L21"
      ],
      "summary": "Tableau-count z-bound certificate.",
      "statement": "Lemma 5.22 proves that weight-zero entries are never a majority.",
      "terms": [
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L07"
        },
        {
          "text": "Counting one more matching edge",
          "target": "S05_L21"
        }
      ]
    },
    {
      "id": "S05_L23",
      "label": "Lem 5.23",
      "title": "Where the induction can fail",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_23_WhereTheInductionCanFail.lean",
      "wrappers": [
        "S05_Lem5_23_where_the_induction_can_fail"
      ],
      "deps": [
        "S05_L22"
      ],
      "summary": "Exceptional-shape localization for the even induction.",
      "statement": "Lemma 5.23 identifies where the even certificate induction can fail.",
      "terms": [
        {
          "text": "Weight-zero entries are never a majority",
          "target": "S05_L22"
        }
      ]
    },
    {
      "id": "S05_L24",
      "label": "Lem 5.24",
      "title": "Even certificate",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_24_EvenCertificate.lean",
      "wrappers": [
        "S05_Lem5_24_tableau_even_certificate"
      ],
      "deps": [
        "S05_L07",
        "S05_L21",
        "S05_L22",
        "S05_L23"
      ],
      "summary": "Finite even h-bound certificate.",
      "statement": "Lemma 5.24 proves the even finite certificate.",
      "terms": [
        {
          "text": "Two-box dimension recursion",
          "target": "S05_L07"
        },
        {
          "text": "Counting one more matching edge",
          "target": "S05_L21"
        },
        {
          "text": "Weight-zero entries are never a majority",
          "target": "S05_L22"
        },
        {
          "text": "Where the induction can fail",
          "target": "S05_L23"
        }
      ]
    },
    {
      "id": "S05_L25",
      "label": "Lem 5.25",
      "title": "Odd exceptional children",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "normal",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_25_OddExceptionalChildren.lean",
      "wrappers": [
        "S05_Lem5_25_odd_exceptional_children"
      ],
      "deps": [
        "S05_L24"
      ],
      "summary": "Odd exceptional child analysis.",
      "statement": "Lemma 5.25 proves the odd exceptional-children analysis.",
      "terms": [
        {
          "text": "Even certificate",
          "target": "S05_L24"
        }
      ]
    },
    {
      "id": "S05_L26",
      "label": "Lem 5.26",
      "title": "Odd certificate",
      "section": "Finite certificates",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S05_Lem5_26_OddCertificate.lean",
      "wrappers": [
        "S05_Lem5_26_tableau_odd_certificate"
      ],
      "deps": [
        "S05_L08",
        "S05_L24",
        "S05_L25"
      ],
      "summary": "Finite odd h-bound certificate.",
      "statement": "Lemma 5.26 proves the odd finite certificate.",
      "terms": [
        {
          "text": "One-box dimension recursion",
          "target": "S05_L08"
        },
        {
          "text": "Even certificate",
          "target": "S05_L24"
        },
        {
          "text": "Odd exceptional children",
          "target": "S05_L25"
        }
      ]
    },
    {
      "id": "Thm1_1",
      "label": "Thm 1.1",
      "title": "Main theorem",
      "section": "Main spine",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S01_Thm1_01_MainIntro.lean",
      "wrappers": [
        "Thm1_1_MainIntro"
      ],
      "deps": [
        "L4_13"
      ],
      "summary": "Main theorem wrapper, proved from one-trial soundness.",
      "statement": "Thm 1.1: Main theorem wrapper, proved from one-trial soundness.",
      "terms": [
        {
          "text": "One-trial soundness",
          "target": "L4_13"
        }
      ]
    },
    {
      "id": "Thm2_1",
      "label": "Thm 2.1",
      "title": "Boolean U1 classification",
      "section": "External inputs",
      "kind": "external",
      "importance": "normal",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S02_Thm2_01_BooleanU1Classification.lean",
      "wrappers": [
        "Thm2_1_BooleanU1",
        "booleanU1_dictator_classification_input"
      ],
      "deps": [],
      "summary": "External structural classification for Boolean degree-one functions.",
      "statement": "Thm 2.1: External structural classification for Boolean degree-one functions.",
      "terms": [
        {
          "text": "U1",
          "target": "S05_D08"
        }
      ]
    },
    {
      "id": "Thm2_2",
      "label": "Thm 2.2",
      "title": "FKN/stability input",
      "section": "External inputs",
      "kind": "external",
      "importance": "major",
      "status": "external",
      "file": "DictatorshipTesting/Paper/S02_Thm2_02_FKNStability.lean",
      "wrappers": [
        "Thm2_2_FKNInput",
        "fknStability_input"
      ],
      "deps": [],
      "summary": "External Filmus stability theorem in the distance-to-dictators form.",
      "statement": "Thm 2.2: External Filmus stability theorem in the distance-to-dictators form.",
      "terms": []
    },
    {
      "id": "Thm4_10",
      "label": "Thm 4.10",
      "title": "Matching-cube spectral gap",
      "section": "Main spine",
      "kind": "paper",
      "importance": "hero",
      "status": "proven",
      "file": "DictatorshipTesting/Paper/S04_Thm4_10_MatchingGap.lean",
      "wrappers": [
        "Thm4_10_MatchingGap"
      ],
      "deps": [
        "S05_L19",
        "S05_L20"
      ],
      "summary": "The active proof uses the tableauDim spectral bridges and Appendix A spectral-model inputs.",
      "statement": "Thm 4.10: The active proof uses the tableauDim spectral bridges and Appendix A spectral-model inputs.",
      "terms": [
        {
          "text": "Even spectral bridge",
          "target": "S05_L19"
        },
        {
          "text": "Odd spectral bridge",
          "target": "S05_L20"
        },
        {
          "text": "even spectral bridge",
          "target": "S05_L19"
        },
        {
          "text": "odd spectral bridge",
          "target": "S05_L20"
        },
        {
          "text": "Appendix A spectral-model inputs",
          "target": "S05_L18"
        },
        {
          "text": "tableauDim",
          "target": "S05_D04"
        }
      ]
    }
  ]
};
