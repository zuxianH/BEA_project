(* ::Package:: *)

(* Bertini-only single-tableau entry point.
   This keeps the Mathematica symbolic workflow from the original runtime, but
   replaces the Julia continuation backend with the local Python/Bertini driver. *)

Off[FrontEndObject::notavail];

ClearAll[SUSYWBEProjectDirectory];
SUSYWBEProjectDirectory[] := Module[
  {inputDirectory, notebookDirectory},
  inputDirectory = If[
    StringQ[$InputFileName] && $InputFileName =!= "",
    DirectoryName[$InputFileName],
    $Failed
  ];
  notebookDirectory = Quiet[
    Check[NotebookDirectory[], $Failed],
    FrontEndObject::notavail
  ];

  SelectFirst[
    {inputDirectory, notebookDirectory, Directory[]},
    StringQ[#] && DirectoryQ[#] &,
    Directory[]
  ]
];

Get[FileNameJoin[{SUSYWBEProjectDirectory[], "SUSYWBEWorkflow.wl"}]];


ClearAll[
  BertiniEnvString,
  BertiniEnvNumber,
  BertiniEnvTrueQ,
  BertiniEnvIntegerOrAutomatic,
  BertiniPythonExecutable,
  BertiniContinuationScript,
  BertiniNumberString,
  BertiniOptionalCommandArguments,
  BertiniCommand
];

BertiniEnvString[name_String, default_] := Module[{value = Environment[name]},
  If[StringQ[value] && StringTrim[value] =!= "", value, default]
];

BertiniEnvNumber[name_String, default_] := Module[{value = Environment[name], parsed},
  If[!(StringQ[value] && StringTrim[value] =!= ""),
    Return[default]
  ];
  parsed = Quiet@Check[
    ToExpression[StringReplace[StringTrim[value], {"e" -> "*^", "E" -> "*^"}], InputForm],
    $Failed
  ];
  If[NumberQ[parsed], parsed, default]
];

BertiniEnvTrueQ[name_String, default_: False] := Module[
  {value = Environment[name]},
  value = If[StringQ[value], ToLowerCase@StringTrim[value], ""];
  Which[
    MemberQ[{"1", "true", "yes", "on"}, value], True,
    MemberQ[{"0", "false", "no", "off", ""}, value], False,
    True, TrueQ[default]
  ]
];

BertiniEnvIntegerOrAutomatic[name_String] := Module[{value = Environment[name], parsed},
  If[!(StringQ[value] && StringTrim[value] =!= ""),
    Return[Automatic]
  ];
  parsed = Quiet@Check[ToExpression[StringTrim[value], InputForm], $Failed];
  If[IntegerQ[parsed], parsed, Automatic]
];

BertiniPythonExecutable[] := Module[
  {projectDirectory, localPython},
  projectDirectory = SUSYWBEProjectDirectory[];
  localPython = FileNameJoin[{projectDirectory, ".venv", "bin", "python"}];
  If[FileExistsQ[localPython], localPython, "python3"]
];

BertiniContinuationScript[] := FileNameJoin[{
  SUSYWBEProjectDirectory[],
  "continue_lambda0_to_zero.py"
}];

BertiniNumberString[value_] := StringReplace[
  ToString[N[value, 20], InputForm],
  {
    RegularExpression["`[0-9.]*"] -> "",
    "*^" -> "e"
  }
];

If[! ValueQ[$BertiniTrackingTolerance], $BertiniTrackingTolerance = BertiniEnvNumber["BERTINI_TRACKING_TOLERANCE", 1.*^-8]];
If[! ValueQ[$BertiniInfiniteTolerance], $BertiniInfiniteTolerance = BertiniEnvNumber["BERTINI_INFINITE_TOLERANCE", 1.*^8]];
If[! ValueQ[$BertiniDefaultPrecision], $BertiniDefaultPrecision = BertiniEnvIntegerOrAutomatic["BERTINI_DEFAULT_PRECISION"]];
If[! ValueQ[$BertiniMaxPrecision], $BertiniMaxPrecision = BertiniEnvIntegerOrAutomatic["BERTINI_MAX_PRECISION"]];
If[! ValueQ[$BertiniMaxNumSteps], $BertiniMaxNumSteps = BertiniEnvIntegerOrAutomatic["BERTINI_MAX_NUM_STEPS"]];
If[! ValueQ[$BertiniInitialStepSize], $BertiniInitialStepSize = BertiniEnvString["BERTINI_INITIAL_STEP_SIZE", Automatic]];
If[! ValueQ[$BertiniMaxStepSize], $BertiniMaxStepSize = BertiniEnvString["BERTINI_MAX_STEP_SIZE", Automatic]];
If[! ValueQ[$BertiniMaxNewtonIterations], $BertiniMaxNewtonIterations = BertiniEnvIntegerOrAutomatic["BERTINI_MAX_NEWTON_ITERATIONS"]];
If[! ValueQ[$BertiniPredictor], $BertiniPredictor = BertiniEnvString["BERTINI_PREDICTOR", Automatic]];

BertiniOptionalCommandArguments[] := Join[
  If[IntegerQ[$BertiniDefaultPrecision],
    {"--default-precision", ToString[$BertiniDefaultPrecision, InputForm]},
    {}
  ],
  If[IntegerQ[$BertiniMaxPrecision],
    {"--max-precision", ToString[$BertiniMaxPrecision, InputForm]},
    {}
  ],
  If[IntegerQ[$BertiniMaxNumSteps],
    {"--max-num-steps", ToString[$BertiniMaxNumSteps, InputForm]},
    {}
  ],
  If[StringQ[$BertiniInitialStepSize],
    {"--initial-step-size", $BertiniInitialStepSize},
    {}
  ],
  If[StringQ[$BertiniMaxStepSize],
    {"--max-step-size", $BertiniMaxStepSize},
    {}
  ],
  If[IntegerQ[$BertiniMaxNewtonIterations],
    {"--max-newton-iterations", ToString[$BertiniMaxNewtonIterations, InputForm]},
    {}
  ],
  If[StringQ[$BertiniPredictor],
    {"--predictor", $BertiniPredictor},
    {}
  ]
];

BertiniCommand[runConfiguration_Association] := Join[
  {
    BertiniPythonExecutable[],
    BertiniContinuationScript[],
    runConfiguration["InitialDataFile"],
    "--legacy-output",
    "--output",
    runConfiguration["OutputFile"],
    "--timing-file",
    runConfiguration["JuliaTimingFile"],
    "--lambda-column",
    "lambda0",
    "--parameter-symbol",
    "h",
    "--target",
    ToString[\[CapitalLambda]target, InputForm],
    "--tracking-tolerance",
    BertiniNumberString[$BertiniTrackingTolerance],
    "--infinite-tolerance",
    BertiniNumberString[$BertiniInfiniteTolerance]
  },
  BertiniOptionalCommandArguments[]
];


ClearAll[RunBertiniContinuation];
RunBertiniContinuation[SYT_] := Module[
  {
    runConfiguration, outputFile, stdoutFile, stderrFile, timingFile,
    timeout, command, processStart, processSeconds, waitStart, waitSeconds,
    importStart, importSeconds, processResult, bertiniOutput, internalTimings
  },
  runConfiguration = GetJuliaRunConfiguration[];
  outputFile = runConfiguration["OutputFile"];
  stdoutFile = runConfiguration["StdoutFile"];
  stderrFile = runConfiguration["StderrFile"];
  timingFile = runConfiguration["JuliaTimingFile"];
  timeout = Lookup[runConfiguration, "JuliaTimeout", 900];

  If[FileExistsQ[outputFile], Quiet@DeleteFile[outputFile]];
  If[FileExistsQ[timingFile], Quiet@DeleteFile[timingFile]];

  command = BertiniCommand[runConfiguration];
  processStart = AbsoluteTime[];
  processResult = Quiet @ Check[
    TimeConstrained[RunProcess[command, All], timeout, $Aborted],
    $Failed
  ];
  processSeconds = AbsoluteTime[] - processStart;

  If[processResult === $Aborted,
    Export[stdoutFile, "", "String"];
    Export[
      stderrFile,
      "Bertini subprocess exceeded timeout of " <> ToString[timeout] <> " seconds.",
      "String"
    ];
    Return[$Failed]
  ];

  If[AssociationQ[processResult],
    WriteJuliaProcessLogs[stdoutFile, stderrFile, processResult]
  ];

  If[
    processResult === $Failed ||
    Lookup[processResult, "ExitCode", 1] =!= 0,
    Return[$Failed]
  ];

  waitStart = AbsoluteTime[];
  If[! WaitForStableFile[outputFile, Min[30, timeout]],
    Return[$Failed]
  ];
  waitSeconds = AbsoluteTime[] - waitStart;

  importStart = AbsoluteTime[];
  bertiniOutput = ReadJuliaResultVector[];
  importSeconds = AbsoluteTime[] - importStart;
  If[!(ListQ[bertiniOutput] && VectorQ[bertiniOutput, NumericQ]),
    Return[$Failed]
  ];

  internalTimings = ReadJuliaTimingFile[];
  <|
    "Vector" -> bertiniOutput,
    "Timings" -> BuildJuliaTimingAssociation[
      "Bertini",
      runConfiguration,
      <|
        "ProcessSeconds" -> processSeconds,
        "WaitForOutputSeconds" -> waitSeconds,
        "ImportSeconds" -> importSeconds,
        "TotalBackendSeconds" -> processSeconds + importSeconds
      |>,
      internalTimings
    ]
  |>
];


ClearAll[IterateUptdInterimBertini];
IterateUptdInterimBertini[SYT_] := Block[{},
  runConfiguration = GetJuliaRunConfiguration[];
  exportSeconds = First@AbsoluteTiming[exportToJuliaInitialData[SYT]];
  SUSYWBEProgressPrint[
    "Initial norm: ",
    Norm[InterpEqnsUptd[\[CapitalLambda]0] /. sol[\[CapitalLambda]0]]
  ];
  SUSYWBEProgressPrint[
    "First findroot norm: ",
    Norm[(InterpEqnsUptd[\[CapitalLambda]0] // ExpandAll) /. MYminsolrep]
  ];

  backendResult = RunBertiniContinuation[SYT];

  If[AssociationQ[backendResult],
    AppendTo[
      savedJuliaTime,
      Join[
        <|
          "TableauStep" -> SYT,
          "ExportSeconds" -> exportSeconds
        |>,
        Lookup[backendResult, "Timings", <||>]
      ]
    ]
  ];

  bertiniOutput = If[
    AssociationQ[backendResult],
    Lookup[backendResult, "Vector", $Failed],
    $Failed
  ];

  If[!(ListQ[bertiniOutput] && VectorQ[bertiniOutput, NumericQ]),
    Throw[Nothing, "BadBertiniOutput"]
  ];

  minsolrep = Rule @@@ Transpose[{susyvars, SetPrecision[bertiniOutput, prec]}];
  sol[0] = minsolrep;
  AppendTo[\[CapitalLambda]vals, 0];
];


ClearAll[PrintRunFailureSummary];
PrintRunFailureSummary[result_Association] := Module[
  {runEnvironment, timedResult, timingSeconds},
  runEnvironment = Lookup[result, "RunEnvironment", <||>];
  timedResult = Lookup[result, "TimedResult", Missing["NotAvailable"]];
  timingSeconds = Replace[
    timedResult,
    {
      values_List /; Length[values] >= 1 :> First[values],
      other_ :> other
    }
  ];

  Print["Run failed."];
  Print["FailureReason: ", Lookup[result, "FailureReason", "Unknown"]];
  Print["Diagnostic: ", Lookup[result, "Diagnostic", "Unavailable"]];
  Print["RunID: ", Lookup[runEnvironment, "RunID", "Unknown"]];
  Print["Result CSV: ", Lookup[result, "BetheRootsFile", "Not saved"]];
  Print["Bertini stdout log: ", Lookup[runEnvironment, "StdoutFile", "Unavailable"]];
  Print["Bertini stderr log: ", Lookup[runEnvironment, "StderrFile", "Unavailable"]];
  Print["Bertini timing CSV: ", Lookup[runEnvironment, "JuliaTimingFile", "Unavailable"]];

  If[NumberQ[timingSeconds] && timingSeconds < 1,
    Print["The run failed almost immediately. Check the Bertini stderr log above."]
  ];
];


ClearAll[ConvertFromCoefficientToRootsYD];
ConvertFromCoefficientToRootsYD[solc_, localYD_] := Module[
  {solList, allBetheQ, allBetheRootEqns, betheRoots},
  solList = If[
    MatchQ[solc, {(_Rule)...}],
    {solc},
    solc
  ];

  Map[
    Function[sol,
      allBetheQ = Table[YQa[w, 0, localYD], {w, Length[localYD] - 1}] /. sol;
      allBetheRootEqns = Thread[allBetheQ == 0];
      betheRoots = Map[
        Function[eqn,
          Module[{rootSolve = Solve[eqn, u]},
            If[rootSolve === {}, Missing["NoSolution"], u /. rootSolve]
          ]
        ],
        allBetheRootEqns
      ];
      betheRoots
    ],
    solList
  ][[1]]
];


ClearAll[BuildSubSYTResult];
BuildSubSYTResult[result_Association] := Module[
  {tableau, solutionHistory, subTableaux, solutionTriples, usableLength},
  tableau = Lookup[result, "Tableau", Missing["NotAvailable"]];
  solutionHistory = Lookup[result, "TimedResult", Missing["NotAvailable"]];
  If[
    ! ListQ[solutionHistory] || Length[solutionHistory] < 2,
    Return[{}]
  ];

  subTableaux = Quiet@Check[SYTlist[tableau], {}];
  solutionTriples = solutionHistory[[2]];
  usableLength = Min[Length[subTableaux], Length[solutionTriples]];

  Table[
    Module[{subTableau, subYD, coefficientSolution, betheRoots},
      subTableau = subTableaux[[k]];
      subYD = ToYD[subTableau];
      coefficientSolution = solutionTriples[[k, 3]];
      betheRoots = ConvertFromCoefficientToRootsYD[coefficientSolution, subYD];
      <|
        "Tableau" -> subTableau,
        "YoungDiagram" -> subYD,
        "BetheRoots" -> betheRoots
      |>
    ],
    {k, usableLength}
  ]
];


ClearAll[SaveSubSYTResultCSVRows];
SaveSubSYTResultCSVRows[subResult_Association] := {
  {"Tableau", "YoungDiagram", "BetheRoots"},
  {
    ToString[Lookup[subResult, "Tableau", {}], InputForm],
    ToString[Lookup[subResult, "YoungDiagram", {}], InputForm],
    ToString[Lookup[subResult, "BetheRoots", Missing["NotAvailable"]], InputForm]
  }
};


ClearAll[SaveIntermediateSubSYTResults];
SaveIntermediateSubSYTResults[subResults_List, resultDirectory_String] := Module[
  {directory, intermediateResults},
  directory = EnsureSUSYWBEDirectory[resultDirectory];
  intermediateResults = Most[subResults];
  Table[
    Module[{tableau, outputFile},
      tableau = Lookup[subResult, "Tableau", {}];
      outputFile = FileNameJoin[{directory, SYTFileName[tableau]}];
      Export[outputFile, SaveSubSYTResultCSVRows[subResult], "CSV"];
      outputFile
    ],
    {subResult, intermediateResults}
  ]
];


SetMarkedPointSelector[UseRandomMinimalMarkedPoint];
SetSingleSYTRunConfiguration[
  InitialLambda -> BertiniEnvNumber["BERTINI_INITIAL_LAMBDA", 70],
  TargetLambda -> BertiniEnvNumber["BERTINI_TARGET_LAMBDA", 0],
  StartInterpolationOrder -> 2,
  WorkingPrecision -> BertiniEnvNumber["BERTINI_WORKING_PRECISION", 100],
  InterpolationOrder -> 3,
  ContinuationStepSize -> 0.1,
  IteratorFunction -> IterateUptdInterimBertini
];

saveBertiniIntermediateCSVFiles = True;
saveFinalSYTFile = True;
saveAllSubSYT = False;
saveWorkflowTimingCSV = False;
subSYTResultDirectory = BertiniEnvString[
  "BERTINI_RESULT_SYT_DIR",
  FileNameJoin[{SUSYWBEProjectDirectory[], "Result_SYT"}]
];

ClearAll[ValidSYTShapeQ, ParseSYTArgument, RunSingleCommandLineArguments, ResolveRunSingleSYT];
ValidSYTShapeQ[value_] := MatchQ[value, {{__Integer}..}];

ParseSYTArgument[arg_String] := Module[{held},
  held = Quiet@Check[ToExpression[arg, InputForm, HoldComplete], $Failed];
  Replace[
    held,
    {
      HoldComplete[value_] /; ValidSYTShapeQ[value] :> value,
      _ :> $Failed
    }
  ]
];

RunSingleCommandLineArguments[] := Module[
  {scriptArgs, commandLine, inputFile, inputPosition, scriptFlagPosition},
  scriptArgs = If[Length[$ScriptCommandLine] >= 2, Rest[$ScriptCommandLine], {}];
  If[scriptArgs =!= {},
    Return[scriptArgs]
  ];

  commandLine = $CommandLine;
  inputFile = $InputFileName;
  inputPosition = If[
    StringQ[inputFile] && inputFile =!= "",
    FirstPosition[commandLine, inputFile, Missing["NotFound"]],
    Missing["NotFound"]
  ];
  If[ListQ[inputPosition],
    Return[Drop[commandLine, First[inputPosition]]]
  ];

  scriptFlagPosition = FirstPosition[commandLine, "-script", Missing["NotFound"]];
  If[ListQ[scriptFlagPosition],
    Return[Drop[commandLine, First[scriptFlagPosition] + 1]]
  ];

  {}
];

ResolveRunSingleSYT[defaultSYT_List] := Module[{args, parsedSYT},
  args = RunSingleCommandLineArguments[];
  If[args === {},
    Return[defaultSYT]
  ];

  parsedSYT = ParseSYTArgument[StringRiffle[args, " "]];
  If[parsedSYT === $Failed,
    Print["Invalid SYT argument. Use Mathematica InputForm, e.g. '{{1,3,7},{2,5},{4,6}}'."];
    Exit[1]
  ];

  parsedSYT
];

syt = If[
  ValueQ[$BertiniRunSingleSYTOverride],
  $BertiniRunSingleSYTOverride,
  ResolveRunSingleSYT[{{1, 3, 7}, {2, 5}, {4, 6}}]
];
Print["Running SYT with Bertini: ", ToString[syt, InputForm]];

result = RunSingleSYT[
  syt,
  MuteProgress -> True,
  SaveSubSYTCSVFiles -> saveBertiniIntermediateCSVFiles,
  SaveBetheRootsBySYT -> saveFinalSYTFile,
  SaveWorkflowTimingCSV -> saveWorkflowTimingCSV,
  CleanupWorkDir -> BertiniEnvTrueQ["BERTINI_CLEANUP_RUNS"],
  JuliaTimeout -> BertiniEnvNumber["BERTINI_TIMEOUT", 900],
  ResultSYTDirectory -> subSYTResultDirectory
];

If[! TrueQ[Lookup[result, "SucceededQ", False]],
  PrintRunFailureSummary[result];
  Exit[1]
];

subSYTResult = If[
  TrueQ[Lookup[result, "SucceededQ", False]],
  BuildSubSYTResult[result],
  {}
];

savedSubSYTFiles = If[
  saveAllSubSYT && subSYTResult =!= {},
  SaveIntermediateSubSYTResults[subSYTResult, subSYTResultDirectory],
  {}
];

result["BetheRoots"]
