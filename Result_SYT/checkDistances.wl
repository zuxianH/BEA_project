(* ::Package:: *)

(* Compare Bethe roots of each SYT with the negated roots of its KKR flip. *)

$CheckDistancesDirectory = "/home/zuxian/Documents/Bertini/Result_SYT";

Get[FileNameJoin[{$CheckDistancesDirectory, "..", "utils", "functions.m"}]];

ClearAll[
  AggregateRootsFile,
  LoadRootRows,
  LoadRootRowsFile,
  ParseCSVExpression,
  TableauKey,
  FlipSYT,
  CompareFlip,
  CheckFlipRows,
  CheckFlipDistance,
  CheckFlipDistances,
  FalseFlipDistances,
  BertiniFalseFlipDistances,
  ResultDirectory,
  NegateFlippedRoots,
  SameRootsTolerance
];

Options[CheckFlipDistances] = {
  ResultDirectory -> Automatic,
  NegateFlippedRoots -> True,
  SameRootsTolerance -> 10^-10
};
Options[CheckFlipDistance] = Options[CheckFlipDistances];
Options[FalseFlipDistances] = Options[CheckFlipDistances];
Options[BertiniFalseFlipDistances] = Options[CheckFlipDistances];

AggregateRootsFile[yd_List, directory_: Automatic] := FileNameJoin[{
  Replace[directory, Automatic :> $CheckDistancesDirectory],
  "all_SYT_" <>
    StringReplace[ToString[yd, InputForm], WhitespaceCharacter .. -> ""] <>
    ".csv"
}];

ParseCSVExpression[value_] := Quiet @ Check[
  If[StringQ[value], ToExpression[value, InputForm], value],
  $Failed
];

TableauKey[syt_List] :=
  StringReplace[ToString[syt, InputForm], WhitespaceCharacter .. -> ""];

FlipSYT[syt_List] := ToSYT @ FlipConfig @ ToRiggedExact[syt];

LoadRootRowsFile[file_String] := Module[{csv, rows},
  If[! FileExistsQ[file],
    Print["Aggregate roots CSV not found: ", file];
    Return[$Failed]
  ];

  csv = Import[file, "CSV"];
  If[! MatchQ[csv, {header_List, __List}],
    Print["Aggregate roots CSV has no data: ", file];
    Return[$Failed]
  ];

  rows = AssociationThread[First[csv], #] & /@ Rest[csv];
  Select[
    rows,
    ToLowerCase[ToString[Lookup[#, "SucceededQ", False]]] === "true" &
  ]
];

LoadRootRows[yd_List, directory_: Automatic] :=
  LoadRootRowsFile[AggregateRootsFile[yd, directory]];

CompareFlip[
  row_Association,
  index_Integer,
  rowsByTableau_Association,
  negate_,
  tolerance_
] := Module[
  {syt, flipSyt, flipRow, roots, flipRoots, distance},
  syt = ParseCSVExpression[row["Tableau"]];
  flipSyt = FlipSYT[syt];
  flipRow = Lookup[rowsByTableau, TableauKey[flipSyt], Missing["NotFound"]];

  If[MissingQ[flipRow],
    Return[<|
      "Index" -> index,
      "SYT" -> syt,
      "FlipSYT" -> flipSyt,
      "FlipFoundQ" -> False,
      "Distance" -> Missing["FlipSYTNotFound"],
      "SameRootsQ" -> False
    |>]
  ];

  roots = Flatten @ ParseCSVExpression[row["BetheRoots"]];
  flipRoots = Flatten @ ParseCSVExpression[flipRow["BetheRoots"]];
  If[TrueQ[negate], flipRoots = -flipRoots];
  distance = If[
    Length[roots] === Length[flipRoots],
    DistanceMeasure[roots, flipRoots],
    Missing["RootCountMismatch", {Length[roots], Length[flipRoots]}]
  ];

  <|
    "Index" -> index,
    "SYT" -> syt,
    "FlipSYT" -> flipSyt,
    "FlipFoundQ" -> True,
    "Distance" -> distance,
    "SameRootsQ" -> TrueQ[NumericQ[distance] && distance <= tolerance]
  |>
];

CheckFlipRows[rows_List, negate_, tolerance_] := Module[{rowsByTableau},
  rowsByTableau = Association @ Map[
    TableauKey[ParseCSVExpression[#1["Tableau"]]] -> #1 &,
    rows
  ];
  MapIndexed[
    CompareFlip[#1, First[#2], rowsByTableau, negate, tolerance] &,
    rows
  ]
];

CheckFlipDistances[yd : {__Integer}, OptionsPattern[]] := Module[{rows},
  rows = LoadRootRows[yd, OptionValue[ResultDirectory]];
  If[rows === $Failed, Return[$Failed]];
  CheckFlipRows[
    rows,
    TrueQ[OptionValue[NegateFlippedRoots]],
    OptionValue[SameRootsTolerance]
  ]
];

CheckFlipDistances[file_String, OptionsPattern[]] := Module[{rows},
  rows = LoadRootRowsFile[ExpandFileName[file]];
  If[rows === $Failed, Return[$Failed]];
  CheckFlipRows[
    rows,
    TrueQ[OptionValue[NegateFlippedRoots]],
    OptionValue[SameRootsTolerance]
  ]
];

CheckFlipDistance[syt : {__List}, OptionsPattern[]] := Module[
  {results},
  results = CheckFlipDistances[
    Length /@ syt,
    ResultDirectory -> OptionValue[ResultDirectory],
    NegateFlippedRoots -> OptionValue[NegateFlippedRoots],
    SameRootsTolerance -> OptionValue[SameRootsTolerance]
  ];
  If[results === $Failed, Return[$Failed]];
  SelectFirst[results, #1["SYT"] === syt &, Missing["SYTNotFound"]]
];

FalseFlipDistances[yd : {__Integer}, opts : OptionsPattern[]] := Module[
  {results},
  results = CheckFlipDistances[yd, opts];
  If[results === $Failed, Return[$Failed]];
  Lookup[#1, {"Index", "SYT", "FlipSYT", "Distance", "SameRootsQ"}] & /@
    Select[results, TrueQ[#1["FlipFoundQ"]] && ! TrueQ[#1["SameRootsQ"]] &]
];

FalseFlipDistances[file_String, opts : OptionsPattern[]] := Module[{results},
  results = CheckFlipDistances[file, opts];
  If[results === $Failed, Return[$Failed]];
  Lookup[#1, {"Index", "SYT", "FlipSYT", "Distance", "SameRootsQ"}] & /@
    Select[results, TrueQ[#1["FlipFoundQ"]] && ! TrueQ[#1["SameRootsQ"]] &]
];

BertiniFalseFlipDistances[file_String, opts : OptionsPattern[]] :=
  FalseFlipDistances[file, opts];

FalseFlipDistances[syt : {__List}, opts : OptionsPattern[]] := Module[
  {result = CheckFlipDistance[syt, opts]},
  If[AssociationQ[result] && ! TrueQ[result["SameRootsQ"]],
    {Lookup[result, {"Index", "SYT", "FlipSYT", "Distance", "SameRootsQ"}]},
    {}
  ]
];


FalseFlipDistances[{11,5}]



NumberOfTableaux[{11,5}]
