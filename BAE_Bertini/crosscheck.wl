(* Helper for crosscheck.sh. *)

ClearAll[ScriptArguments, ParseInputForm, WriteReport];

ScriptArguments[] := Module[{position},
  If[Length[$ScriptCommandLine] >= 2, Return[Rest[$ScriptCommandLine]]];
  position = FirstPosition[$CommandLine, "-script", Missing["NotFound"]];
  If[ListQ[position], Drop[$CommandLine, First[position] + 1], {}]
];

ParseInputForm[text_String, pattern_] := Module[{held},
  held = Quiet @ Check[ToExpression[text, InputForm, HoldComplete], $Failed];
  Replace[held, {
    HoldComplete[value_] /; MatchQ[value, pattern] :> value,
    _ :> $Failed
  }]
];

WriteReport[path_String, entries_List] := Export[
  path,
  StringRiffle[(ToString[First[#]] <> "=" <> ToString[Last[#], InputForm]) & /@ entries, "\n"] <> "\n",
  "Text"
];

args = ScriptArguments[];
If[args === {}, Print["Missing mode: flip or compare."]; Exit[2]];

Switch[First[args],
  "flip",
  If[Length[args] =!= 3, Print["flip requires SYT and output file."]; Exit[2]];
  Get[FileNameJoin[{DirectoryName[$InputFileName], "utils", "functions.m"}]];
  syt = ParseInputForm[args[[2]], {{__Integer} ..}];
  If[syt === $Failed, Print["Invalid SYT: ", args[[2]]]; Exit[2]];
  flip = ToSYT @ FlipConfig @ ToRiggedExact[syt];
  Export[args[[3]], ToString[flip, InputForm] <> "\n", "Text"];
  Exit[0],

  "compare",
  If[Length[args] =!= 5,
    Print["compare requires aggregate CSV, SYT, tolerance, and report file."];
    Exit[2]
  ];
  Get[FileNameJoin[{DirectoryName[$InputFileName], "Result_SYT", "checkDistances.wl"}]];
  aggregateFile = ExpandFileName[args[[2]]];
  syt = ParseInputForm[args[[3]], {{__Integer} ..}];
  tolerance = ParseInputForm[
    StringReplace[args[[4]], {"e" -> "*^", "E" -> "*^"}],
    _?NumericQ
  ];
  reportFile = args[[5]];
  If[syt === $Failed || tolerance === $Failed,
    Print["Invalid SYT or tolerance."];
    Exit[2]
  ];

  comparisons = CheckFlipDistances[
    aggregateFile,
    NegateFlippedRoots -> True,
    SameRootsTolerance -> tolerance
  ];
  If[comparisons === $Failed, Exit[2]];
  comparison = SelectFirst[
    comparisons,
    Lookup[#, "SYT", Missing[]] === syt &,
    Missing["SYTNotFound"]
  ];
  If[MissingQ[comparison], Print["SYT not found in aggregate CSV."]; Exit[2]];

  rows = LoadRootRowsFile[aggregateFile];
  rowsByTableau = Association[
    TableauKey[ParseCSVExpression[#1["Tableau"]]] -> #1 & /@ rows
  ];
  flip = comparison["FlipSYT"];
  row = Lookup[rowsByTableau, TableauKey[syt], Missing[]];
  flipRow = Lookup[rowsByTableau, TableauKey[flip], Missing[]];
  rootCount = If[MissingQ[row], Missing["NotFound"], Length @ Flatten @ ParseCSVExpression[row["BetheRoots"]]];
  flipRootCount = If[MissingQ[flipRow], Missing["NotFound"], Length @ Flatten @ ParseCSVExpression[flipRow["BetheRoots"]]];
  passed = TrueQ[comparison["SameRootsQ"]];

  WriteReport[reportFile, {
    "SYT" -> syt,
    "FlipSYT" -> flip,
    "Comparison" -> "D[Roots[SYT], -Roots[FlipSYT]]",
    "RootCount" -> rootCount,
    "FlipRootCount" -> flipRootCount,
    "FlipFoundQ" -> comparison["FlipFoundQ"],
    "Distance" -> comparison["Distance"],
    "Tolerance" -> tolerance,
    "Passed" -> passed,
    "AggregateFile" -> aggregateFile
  }];
  Exit[If[passed, 0, 1]],

  _,
  Print["Unknown mode: ", First[args]];
  Exit[2]
]
