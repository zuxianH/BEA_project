(* ::Package:: *)

(* High-level workflow helpers for the SUSY Wronskian Bethe-ansatz project.
   This layer keeps the symbolic and numerical core intact while making the
   main execution path explicit and easier to revisit. *)

SUSYWBEProjectDirectory::usage =
  "SUSYWBEProjectDirectory[] returns the directory that contains the project files.";

SUSYWBEUtilsDirectory::usage =
  "SUSYWBEUtilsDirectory[] returns the directory that contains Mathematica utility files.";

SUSYWBESolverDirectory::usage =
  "SUSYWBESolverDirectory[] returns the directory that contains Mathematica solver modules.";

SUSYWBEJuliaDirectory::usage =
  "SUSYWBEJuliaDirectory[] returns the directory that contains Julia runtime scripts.";

LoadSUSYWBEProjectDependencies::usage =
  "LoadSUSYWBEProjectDependencies[] loads the project-local package dependencies exactly once.";

UseLeftmostBosonicMarkedPoint::usage =
  "UseLeftmostBosonicMarkedPoint[yd] chooses the deterministic marked point {Length[yd], 0}.";

UseRandomMaximalMarkedPoint::usage =
  "UseRandomMaximalMarkedPoint[yd] chooses a random maximal admissible marked point with a > s.";

UseRandomMinimalMarkedPoint::usage =
  "UseRandomMinimalMarkedPoint[yd] chooses a random minimal admissible marked point with a > s.";

SetMarkedPointSelector::usage =
  "SetMarkedPointSelector[selector] configures which marked-point rule GenerateSUSYWsystem uses.";

GetMarkedPointSelector::usage =
  "GetMarkedPointSelector[] returns the currently configured marked-point selector.";

InitialLambda::usage =
  "InitialLambda is the option that sets the large-Lambda starting value used by the numerical solver.";

TargetLambda::usage =
  "TargetLambda is the option that sets the final Lambda value used by the numerical solver.";

StartInterpolationOrder::usage =
  "StartInterpolationOrder is the option that sets the number of large-Lambda seed points.";

InterpolationOrder::usage =
  "InterpolationOrder is the option that sets the interpolation order for predictor-corrector steps.";

ContinuationStepSize::usage =
  "ContinuationStepSize is the option that sets the Lambda step size used by the Mathematica predictor-corrector iterator.";

IteratorFunction::usage =
  "IteratorFunction is the option that selects the continuation iterator, for example IterateUptdInterim.";

WorkDir::usage =
  "WorkDir is the option that sets the task-local working directory used for intermediate files.";

RunID::usage =
  "RunID is the option that sets the identifier used when constructing task-local run directories.";

InitialDataFile::usage =
  "InitialDataFile is the option that sets the explicit CSV path exported for the Julia homotopy input.";

SavedDataDir::usage =
  "SavedDataDir is the option that sets the explicit directory used for Julia-side intermediate and result CSV files.";

OutputFile::usage =
  "OutputFile is the option that sets the explicit CSV path imported after the Julia solve completes.";

SaveSubSYTCSVFiles::usage =
  "SaveSubSYTCSVFiles controls whether per-step sub-tableau CSV snapshots are written inside SavedDataDir during Julia exports.";

StdoutFile::usage =
  "StdoutFile is the option that sets the log file that captures Julia standard output for a single run.";

StderrFile::usage =
  "StderrFile is the option that sets the log file that captures Julia standard error for a single run.";

JuliaTimingFile::usage =
  "JuliaTimingFile is the option that sets the per-run timing CSV written by the Julia backend.";

CleanupWorkDir::usage =
  "CleanupWorkDir is the option that removes a task-local work directory after a successful run when set to True.";

JuliaBackend::usage =
  "JuliaBackend selects the Julia invocation strategy, for example \"ProcessPerRun\", \"PersistentSession\", or \"PersistentSessionSysimage\".";

JuliaTimeout::usage =
  "JuliaTimeout is the option that sets the maximum number of seconds to wait for a blocking Julia subprocess.";

JuliaProcessFlags::usage =
  "JuliaProcessFlags is the option that sets extra command-line flags for Julia CLI backends, for example {\"--threads=1\", \"--compile=min\", \"-O0\"}.";

JuliaSysimagePath::usage =
  "JuliaSysimagePath is the option that sets the custom Julia sysimage path used by sysimage-enabled backends.";

JuliaExecutable::usage =
  "JuliaExecutable is the option that sets the explicit Julia binary or launcher used by CLI-backed backends.";

WorkflowTimingFile::usage =
  "WorkflowTimingFile is the option that sets the per-run workflow timing CSV written into the task-local run directory.";

MuteProgress::usage =
  "MuteProgress suppresses routine progress output when set to True.";

SaveBetheRootsBySYT::usage =
  "SaveBetheRootsBySYT writes one per-tableau Bethe-roots result file as soon as each run finishes.";

SaveWorkflowTimingCSV::usage =
  "SaveWorkflowTimingCSV writes a per-run workflow timing CSV into the task-local run directory when set to True.";

ResultSYTDirectory::usage =
  "ResultSYTDirectory sets the folder where per-tableau Bethe-roots result files are saved.";

CollectRunResults::usage =
  "CollectRunResults controls whether RunAllSYTParallel returns every per-tableau result to the master kernel. Set to False for low-memory streaming runs that save per-tableau CSV files.";

DefaultFastJuliaProcessFlags::usage =
  "DefaultFastJuliaProcessFlags[] returns the validated low-overhead Julia CLI flags used by the optimized workflow.";

PreferredJuliaBackendOptions::usage =
  "PreferredJuliaBackendOptions[] returns the recommended Julia backend option rules, preferring a sysimage-backed persistent worker when the sysimage is available.";

SetSingleSYTRunConfiguration::usage =
  "SetSingleSYTRunConfiguration[opts] writes the numerical run configuration to the globals used by the legacy solver.";

GetSingleSYTRunConfiguration::usage =
  "GetSingleSYTRunConfiguration[] returns the current numerical run configuration as an Association.";

BuildSUSYWSystemData::usage =
  "BuildSUSYWSystemData[yd] constructs the symbolic Wronskian/Q-system data needed by the numerical solver.";

GenerateSUSYWsystem::usage =
  "GenerateSUSYWsystem[yd] populates the legacy global solver state for the given Young diagram and returns the constructed system data.";

RunSingleSYT::usage =
  "RunSingleSYT[syt, opts] solves one standard Young tableau with the current or supplied run configuration and returns an Association of results.";

RunSingleSYTSafe::usage =
  "RunSingleSYTSafe[syt, opts] runs RunSingleSYT with task-local file paths and isolated legacy configuration state.";

RunAllSYTSerial::usage =
  "RunAllSYTSerial[ydOrTableaux, opts] evaluates all tableaux serially with task-local file isolation.";

RunAllSYTParallel::usage =
  "RunAllSYTParallel[ydOrTableaux, opts] evaluates all tableaux in parallel with task-local file isolation.";

singleSYTresultUNIK::usage =
  "singleSYTresultUNIK[syt] preserves the legacy single-tableau entry point while routing configuration through SetSingleSYTRunConfiguration.";

ExtractBetheRootsFromCoefficients::usage =
  "ExtractBetheRootsFromCoefficients[yd, coeffs] solves the Bethe Q-polynomials for an explicit coefficient solution.";

ExtractBetheRootsFromSolutionHistory::usage =
  "ExtractBetheRootsFromSolutionHistory[history, yd] extracts Bethe roots from the final coefficient solution in a solver history.";

ValidSolutionHistoryQ::usage =
  "ValidSolutionHistoryQ[history] returns True when the solver produced a non-empty nested history suitable for Bethe-root extraction.";

NormalizeBetheRoots::usage =
  "NormalizeBetheRoots[data, tol] canonicalizes root ordering for stable comparisons.";

BetheRootsEquivalentQ::usage =
  "BetheRootsEquivalentQ[left, right, tol] compares two Bethe-root collections after canonicalization.";

MaxBetheRootDifference::usage =
  "MaxBetheRootDifference[left, right, tol] returns the maximum absolute difference after canonicalization, or Infinity for mismatched shapes.";

ValidateSYTRunResults::usage =
  "ValidateSYTRunResults[serialRun, parallelRun, reference, tol] compares serial, parallel, and reference Bethe-root collections and returns a concise report.";


ClearAll[NormalizeSUSYWBEProjectDirectoryCandidate];
NormalizeSUSYWBEProjectDirectoryCandidate[path_] := Module[{parts},
  If[!(StringQ[path] && DirectoryQ[path]),
    Return[$Failed]
  ];
  parts = FileNameTake[path];
  If[MemberQ[{"solver", "utils", "julia"}, parts],
    DirectoryName[path],
    path
  ]
];


If[! ValueQ[$SUSYWBEMuteProgress], $SUSYWBEMuteProgress = False];

ClearAll[SUSYWBEProgressPrint];
SUSYWBEProgressPrint[args___] := If[! TrueQ[$SUSYWBEMuteProgress], Print[args]];


ClearAll[EnsureSUSYWBEDirectory];
EnsureSUSYWBEDirectory[path_String] := Module[{expandedPath},
  expandedPath = ExpandFileName[path];
  If[
    ! DirectoryQ[expandedPath],
    Quiet@Check[
      CreateDirectory[expandedPath, CreateIntermediateDirectories -> True],
      Null
    ]
  ];
  expandedPath
];


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
    NormalizeSUSYWBEProjectDirectoryCandidate /@ {inputDirectory, notebookDirectory, Directory[]},
    StringQ[#] && DirectoryQ[#] &,
    Directory[]
  ]
];


SUSYWBEUtilsDirectory[] := FileNameJoin[{SUSYWBEProjectDirectory[], "utils"}];
SUSYWBESolverDirectory[] := FileNameJoin[{SUSYWBEProjectDirectory[], "solver"}];
SUSYWBEJuliaDirectory[] := FileNameJoin[{SUSYWBEProjectDirectory[], "julia"}];


$SUSYWBEProjectRoot = SUSYWBEProjectDirectory[];


LoadSUSYWBEProjectDependencies[] := Module[{projectDirectory},
  If[TrueQ[$SUSYWBEProjectDependenciesLoaded],
    Return[$SUSYWBEProjectDependenciesLoaded]
  ];

  projectDirectory = SUSYWBEProjectDirectory[];

  Get[FileNameJoin[{projectDirectory, "utils", "functions.m"}]];
  Get[FileNameJoin[{projectDirectory, "solver", "SusyWronskianSolver.m"}]];
  Get[FileNameJoin[{projectDirectory, "solver", "NumericalWBE_SUSY.m"}]];

  $SUSYWBEProjectDependenciesLoaded = True
];


LoadSUSYWBEProjectDependencies[];


UseLeftmostBosonicMarkedPoint[yd_List] := {Length[yd], 0};

UseRandomMaximalMarkedPoint[yd_List] := RandomSample[
  MaximalBy[Select[Endpoints[yd], #[[1]] > #[[2]] &], Total],
  1
][[1]];

UseRandomMinimalMarkedPoint[yd_List] := RandomSample[
  MinimalBy[Select[Endpoints[yd], #[[1]] > #[[2]] &], Total],
  1
][[1]];


SetMarkedPointSelector[selector_ : UseLeftmostBosonicMarkedPoint] := Module[{},
  ClearAll[mPfunction];
  mPfunction[yd_] := selector[yd];
  $SUSYWBEMarkedPointSelector = selector;
  selector
];


GetMarkedPointSelector[] := If[
  ValueQ[$SUSYWBEMarkedPointSelector],
  $SUSYWBEMarkedPointSelector,
  SetMarkedPointSelector[]
];


ClearAll[GetJuliaRunConfiguration];
GetJuliaRunConfiguration[] := Module[{projectDirectory, savedDataDir},
  projectDirectory = SUSYWBEProjectDirectory[];
  savedDataDir = FileNameJoin[{projectDirectory, "saved_data"}];
  If[
    AssociationQ[$SUSYWBEJuliaRunConfiguration],
    $SUSYWBEJuliaRunConfiguration,
    <|
      "RunID" -> "default",
      "WorkDir" -> projectDirectory,
      "SavedDataDir" -> savedDataDir,
      "InitialDataFile" -> FileNameJoin[{savedDataDir, "initial_data.csv"}],
      "OutputFile" -> FileNameJoin[{savedDataDir, "output.csv"}],
      "SaveSubSYTCSVFiles" -> True,
      "StdoutFile" -> FileNameJoin[{projectDirectory, "julia.stdout.log"}],
      "StderrFile" -> FileNameJoin[{projectDirectory, "julia.stderr.log"}],
      "JuliaTimingFile" -> FileNameJoin[{projectDirectory, "julia.timings.csv"}],
      "WorkflowTimingFile" -> FileNameJoin[{projectDirectory, "workflow.timings.csv"}],
      "CleanupWorkDir" -> False,
      "JuliaBackend" -> "ProcessPerRun",
      "JuliaTimeout" -> 900,
      "JuliaProcessFlags" -> {"--threads=1"},
      "JuliaSysimagePath" -> None,
      "JuliaExecutable" -> Automatic
    |>
  ]
];


Options[SetSingleSYTRunConfiguration] = {
  InitialLambda -> 20,
  TargetLambda -> 0,
  StartInterpolationOrder -> 2,
  WorkingPrecision -> 40,
  InterpolationOrder -> 3,
  ContinuationStepSize -> 0.1,
  IteratorFunction -> Automatic
};


SetSingleSYTRunConfiguration[OptionsPattern[]] := Module[
  {iterator, configuration},
  iterator = Replace[
    OptionValue[IteratorFunction],
    Automatic :> If[ValueQ[$CurrentIterator], $CurrentIterator, IterateUptdInterim]
  ];

  configuration = <|
    InitialLambda -> OptionValue[InitialLambda],
    TargetLambda -> OptionValue[TargetLambda],
    StartInterpolationOrder -> OptionValue[StartInterpolationOrder],
    WorkingPrecision -> OptionValue[WorkingPrecision],
    InterpolationOrder -> OptionValue[InterpolationOrder],
    ContinuationStepSize -> OptionValue[ContinuationStepSize],
    IteratorFunction -> iterator
  |>;

  \[CapitalLambda]0Interim = configuration[InitialLambda];
  \[CapitalLambda]target = configuration[TargetLambda];
  startinterpord = configuration[StartInterpolationOrder];
  prec = configuration[WorkingPrecision];
  interpord = configuration[InterpolationOrder];
  step = configuration[ContinuationStepSize];
  $CurrentIterator = configuration[IteratorFunction];

  $SUSYWBECurrentRunConfiguration = configuration;
  configuration
];


GetSingleSYTRunConfiguration[] := If[
  AssociationQ[$SUSYWBECurrentRunConfiguration],
  $SUSYWBECurrentRunConfiguration,
  SetSingleSYTRunConfiguration[]
];


ClearAll[DefaultJuliaSysimageExtension];
DefaultJuliaSysimageExtension[] := Which[
  $OperatingSystem === "Windows", ".dll",
  $OperatingSystem === "MacOSX", ".dylib",
  True, ".so"
];


ClearAll[DefaultJuliaSysimagePath];
DefaultJuliaSysimagePath[] := FileNameJoin[{
  SUSYWBEProjectDirectory[],
  ".sysimages",
  "susywbe_worker" <> DefaultJuliaSysimageExtension[]
}];


ClearAll[DefaultFastJuliaProcessFlags];
DefaultFastJuliaProcessFlags[] := {"--threads=1", "--compile=min", "-O0"};


ClearAll[DefaultResultSYTDirectory];
DefaultResultSYTDirectory[] := FileNameJoin[{SUSYWBEProjectDirectory[], "Result_SYT"}];


ClearAll[PreferredJuliaBackendOptions];
PreferredJuliaBackendOptions[] := Module[{sysimagePath = DefaultJuliaSysimagePath[]},
  If[
    FileExistsQ[sysimagePath],
    {
      JuliaBackend -> "PersistentSessionSysimage",
      JuliaProcessFlags -> DefaultFastJuliaProcessFlags[],
      JuliaSysimagePath -> sysimagePath
    },
    {
      JuliaBackend -> "PersistentSession",
      JuliaProcessFlags -> DefaultFastJuliaProcessFlags[]
    }
  ]
];


ClearAll[NormalizeRunID];
NormalizeRunID[value_] := StringReplace[
  ToString[Replace[value, Automatic :> CreateUUID["syt-"]]],
  {
    WhitespaceCharacter .. -> "",
    "\"" -> "",
    "/" -> "_",
    "\\" -> "_",
    ":" -> "_"
  }
];


ClearAll[BuildSYTRunEnvironment];
Options[BuildSYTRunEnvironment] = {
  WorkDir -> Automatic,
  RunID -> Automatic,
  InitialDataFile -> Automatic,
  SavedDataDir -> Automatic,
  OutputFile -> Automatic,
  SaveSubSYTCSVFiles -> Automatic,
  StdoutFile -> Automatic,
  StderrFile -> Automatic,
  JuliaTimingFile -> Automatic,
  WorkflowTimingFile -> Automatic,
  CleanupWorkDir -> False,
  JuliaBackend -> Automatic,
  JuliaTimeout -> Automatic,
  JuliaProcessFlags -> Automatic,
  JuliaSysimagePath -> Automatic,
  JuliaExecutable -> Automatic
};

BuildSYTRunEnvironment[OptionsPattern[]] := Module[
  {
    runID, workDir, savedDataDir, initialDataFile, outputFile,
    saveSubSYTCSVFiles, stdoutFile, stderrFile, juliaTimingFile,
    workflowTimingFile,
    juliaBackend, juliaTimeout, juliaProcessFlags, juliaSysimagePath,
    juliaExecutable
  },
  runID = NormalizeRunID[OptionValue[RunID]];
  workDir = Replace[
    OptionValue[WorkDir],
    Automatic :> FileNameJoin[{SUSYWBEProjectDirectory[], ".runs", runID}]
  ];
  savedDataDir = Replace[
    OptionValue[SavedDataDir],
    Automatic :> FileNameJoin[{workDir, "saved_data"}]
  ];
  initialDataFile = Replace[
    OptionValue[InitialDataFile],
    Automatic :> FileNameJoin[{savedDataDir, "initial_data.csv"}]
  ];
  outputFile = Replace[
    OptionValue[OutputFile],
    Automatic :> FileNameJoin[{savedDataDir, "output.csv"}]
  ];
  saveSubSYTCSVFiles = Replace[
    OptionValue[SaveSubSYTCSVFiles],
    Automatic :> True
  ];
  stdoutFile = Replace[
    OptionValue[StdoutFile],
    Automatic :> FileNameJoin[{workDir, "julia.stdout.log"}]
  ];
  stderrFile = Replace[
    OptionValue[StderrFile],
    Automatic :> FileNameJoin[{workDir, "julia.stderr.log"}]
  ];
  juliaTimingFile = Replace[
    OptionValue[JuliaTimingFile],
    Automatic :> FileNameJoin[{workDir, "julia.timings.csv"}]
  ];
  workflowTimingFile = Replace[
    OptionValue[WorkflowTimingFile],
    Automatic :> FileNameJoin[{workDir, "workflow.timings.csv"}]
  ];
  juliaBackend = Replace[OptionValue[JuliaBackend], Automatic :> "ProcessPerRun"];
  juliaTimeout = Replace[OptionValue[JuliaTimeout], Automatic :> 900];
  juliaProcessFlags = Replace[OptionValue[JuliaProcessFlags], Automatic :> {"--threads=1"}];
  juliaSysimagePath = Replace[
    OptionValue[JuliaSysimagePath],
    {
      Automatic :> If[juliaBackend === "PersistentSessionSysimage", DefaultJuliaSysimagePath[], None],
      None -> None,
      path_String :> ExpandFileName[path]
    }
  ];
  juliaExecutable = Replace[
    OptionValue[JuliaExecutable],
    {
      Automatic :> Automatic,
      path_String /; StringTrim[path] === "" :> Automatic,
      path_String /; StringContainsQ[path, "/"] || StringContainsQ[path, "\\"] || StringStartsQ[path, "."] :> ExpandFileName[path],
      path_String :> StringTrim[path]
    }
  ];

  If[
    ! DirectoryQ[savedDataDir],
    CreateDirectory[savedDataDir, CreateIntermediateDirectories -> True]
  ];
  If[
    ! DirectoryQ[DirectoryName[stdoutFile]],
    CreateDirectory[DirectoryName[stdoutFile], CreateIntermediateDirectories -> True]
  ];
  If[
    ! DirectoryQ[DirectoryName[stderrFile]],
    CreateDirectory[DirectoryName[stderrFile], CreateIntermediateDirectories -> True]
  ];

  <|
    "RunID" -> runID,
    "WorkDir" -> workDir,
    "SavedDataDir" -> savedDataDir,
    "InitialDataFile" -> initialDataFile,
    "OutputFile" -> outputFile,
    "SaveSubSYTCSVFiles" -> TrueQ[saveSubSYTCSVFiles],
    "StdoutFile" -> stdoutFile,
    "StderrFile" -> stderrFile,
    "JuliaTimingFile" -> juliaTimingFile,
    "WorkflowTimingFile" -> workflowTimingFile,
    "CleanupWorkDir" -> TrueQ[OptionValue[CleanupWorkDir]],
    "JuliaBackend" -> juliaBackend,
    "JuliaTimeout" -> juliaTimeout,
    "JuliaProcessFlags" -> juliaProcessFlags,
    "JuliaSysimagePath" -> juliaSysimagePath,
    "JuliaExecutable" -> juliaExecutable
  |>
];


ClearAll[ResolveTableauxInput];
ResolveTableauxInput[input_List] /; VectorQ[input, IntegerQ] := Tableaux[input];
ResolveTableauxInput[input_List] := input;


ClearAll[TaskRunID];
TaskRunID[index_Integer, tableau_List] := StringTemplate["task-`1`-`2`"][
  IntegerString[index, 10, 3],
  IntegerString[Hash[HoldForm[tableau], "SHA256"], 16, 12]
];


ClearAll[BuildTaskScopedRunOptions];
BuildTaskScopedRunOptions[index_Integer, tableau_List, baseOptions_List] := Module[
  {
    runID, workDirOption, savedDataDirOption, initialDataFileOption,
    outputFileOption, stdoutFileOption, stderrFileOption, juliaTimingFileOption,
    workflowTimingFileOption, workDirRule, savedDataDirRule, initialDataFileRule,
    outputFileRule, stdoutFileRule, stderrFileRule, juliaTimingFileRule,
    workflowTimingFileRule, scopedPath
  },
  runID = TaskRunID[index, tableau];
  workDirOption = Replace[WorkDir /. baseOptions, WorkDir -> Automatic];
  savedDataDirOption = Replace[SavedDataDir /. baseOptions, SavedDataDir -> Automatic];
  initialDataFileOption = Replace[InitialDataFile /. baseOptions, InitialDataFile -> Automatic];
  outputFileOption = Replace[OutputFile /. baseOptions, OutputFile -> Automatic];
  stdoutFileOption = Replace[StdoutFile /. baseOptions, StdoutFile -> Automatic];
  stderrFileOption = Replace[StderrFile /. baseOptions, StderrFile -> Automatic];
  juliaTimingFileOption = Replace[JuliaTimingFile /. baseOptions, JuliaTimingFile -> Automatic];
  workflowTimingFileOption = Replace[WorkflowTimingFile /. baseOptions, WorkflowTimingFile -> Automatic];

  scopedPath[filename_String] := Module[{directory, stem, extension},
    directory = DirectoryName[filename];
    stem = FileBaseName[filename];
    extension = FileExtension[filename];
    FileNameJoin[{
      directory,
      stem <> "-" <> runID <> If[extension === "", "", "." <> extension]
    }]
  ];

  workDirRule = WorkDir -> Replace[
    workDirOption,
    {
      Automatic :> Automatic,
      directory_String :> FileNameJoin[{directory, runID}]
    }
  ];
  savedDataDirRule = SavedDataDir -> Replace[
    savedDataDirOption,
    {
      Automatic :> Automatic,
      directory_String :> FileNameJoin[{directory, runID}]
    }
  ];
  initialDataFileRule = InitialDataFile -> Replace[
    initialDataFileOption,
    {
      Automatic :> Automatic,
      filename_String :> scopedPath[filename]
    }
  ];
  outputFileRule = OutputFile -> Replace[
    outputFileOption,
    {
      Automatic :> Automatic,
      filename_String :> scopedPath[filename]
    }
  ];
  stdoutFileRule = StdoutFile -> Replace[
    stdoutFileOption,
    {
      Automatic :> Automatic,
      filename_String :> scopedPath[filename]
    }
  ];
  stderrFileRule = StderrFile -> Replace[
    stderrFileOption,
    {
      Automatic :> Automatic,
      filename_String :> scopedPath[filename]
    }
  ];
  juliaTimingFileRule = JuliaTimingFile -> Replace[
    juliaTimingFileOption,
    {
      Automatic :> Automatic,
      filename_String :> scopedPath[filename]
    }
  ];
  workflowTimingFileRule = WorkflowTimingFile -> Replace[
    workflowTimingFileOption,
    {
      Automatic :> Automatic,
      filename_String :> scopedPath[filename]
    }
  ];

  {
    RunID -> runID,
    workDirRule,
    savedDataDirRule,
    initialDataFileRule,
    outputFileRule,
    stdoutFileRule,
    stderrFileRule,
    juliaTimingFileRule,
    workflowTimingFileRule
  }
];


ClearAll[SetSUSYWSystemState];
SetSUSYWSystemState[systemData_Association] := Module[{},
  mP = systemData["MarkedPoint"];
  susyvars = systemData["SusyVariables"];
  AllrelWronskian = systemData["WronskianRelations"];
  allsusycoeff = systemData["SusyToCCoefficients"];
  c2susycoeff = systemData["CToSusyCoefficients"];
  $SUSYWBECurrentSystem = systemData;
  systemData
];


BuildSUSYWSystemData[yd_List] := Module[
  {
    markedPoint,
    susyResult,
    susyWronskian,
    thetaPolynomial,
    susyVariables,
    selectedPath,
    wronskianRelations,
    susyToCCoefficients,
    cToSusyCoefficients
  },
  (* Rebuild the Q-system explicitly for this Young diagram so the workflow
     does not depend on previously initialized global state. *)
  GenerateQsystem[yd];

  markedPoint = mPfunction[yd];
  susyResult = GenerateSusyWronskian[markedPoint, yd];
  susyWronskian = susyResult["SusyWronskian"];
  thetaPolynomial = susyResult["YQ\[Theta]"];
  susyVariables = Rest[Variables[susyWronskian]];

  (* TODO: verify original intent. The legacy code used Intersection[...]//Reverse,
     which sorts the path data rather than preserving traversal order. *)
  selectedPath = Intersection[
    Select[AllPaths[yd], Last[#] === markedPoint &][[1]],
    DomainOfInterest
  ] // Reverse;

  wronskianRelations =
    CoefficientList[YQa[0, 0, yd] - Getmonic[susyWronskian], u] //
      Expand //
      (# /. Complex[0, b_] :> b) &;

  (* Legacy coefficient-conversion code relies on dynamically scoped globals
     mP and susyvars even though the marked point and variable list are also
     passed around as explicit values. *)
  {susyToCCoefficients, cToSusyCoefficients} = Block[
    {mP = markedPoint, susyvars = susyVariables},
    {
      Computesusy2cCoefficientsv3[yd, markedPoint],
      Computec2susyCoefficientsv2[yd, markedPoint]
    }
  ];

  <|
    "YoungDiagram" -> yd,
    "MarkedPoint" -> markedPoint,
    "WronskianData" -> susyResult,
    "SusyWronskian" -> susyWronskian,
    "ThetaPolynomial" -> thetaPolynomial,
    "SusyVariables" -> susyVariables,
    "SelectedPath" -> selectedPath,
    "WronskianRelations" -> wronskianRelations,
    "SusyToCCoefficients" -> susyToCCoefficients,
    "CToSusyCoefficients" -> cToSusyCoefficients
  |>
];


GenerateSUSYWsystem[yd_List] := Module[{systemData},
  systemData = SetSUSYWSystemState[BuildSUSYWSystemData[yd]];
  SUSYWBEProgressPrint["System generated for mP: ", systemData["MarkedPoint"]];
  systemData
];


ClearAll[SYTFileName];
SYTFileName[tableau_List] := ToString[tableau, InputForm] <> ".csv";


ClearAll[SavedBetheRootsPayload];
SavedBetheRootsPayload[result_Association] := Module[{betheRoots},
  betheRoots = Lookup[result, "BetheRoots", Missing["NotAvailable"]];
  If[ListQ[betheRoots] && Length[betheRoots] == 1, First[betheRoots], betheRoots]
];


ClearAll[ReadDiagnosticTail];
ReadDiagnosticTail[path_, maxCharacters_: 1200] := Module[{text},
  If[! StringQ[path] || ! FileExistsQ[path],
    Return[""]
  ];
  text = Quiet@Check[Import[path, "Text"], ""];
  If[! StringQ[text] || StringLength[StringTrim[text]] == 0,
    Return[""]
  ];
  StringTake[StringTrim[text], -Min[maxCharacters, StringLength[StringTrim[text]]]]
];


ClearAll[BuildRunFailureDiagnostic];
BuildRunFailureDiagnostic[result_Association] := Module[
  {
    runEnvironment, solutionHistory, expectedStageCount, completedStageCount,
    failureReason, stderrTail, stdoutTail
  },
  If[TrueQ[Lookup[result, "SucceededQ", False]],
    Return[""]
  ];

  runEnvironment = Lookup[result, "RunEnvironment", <||>];
  solutionHistory = Lookup[result, "SolutionHistory", {}];
  expectedStageCount = Quiet@Check[
    Length[SYTlist[Lookup[result, "Tableau", {}]]],
    Missing["NotAvailable"]
  ];
  completedStageCount = If[ListQ[solutionHistory], Length[solutionHistory], 0];
  failureReason = ToString[Lookup[result, "FailureReason", "Unknown"], InputForm];
  stderrTail = ReadDiagnosticTail[Lookup[runEnvironment, "StderrFile", ""]];
  stdoutTail = ReadDiagnosticTail[Lookup[runEnvironment, "StdoutFile", ""]];

  StringRiffle[
    DeleteCases[
      {
        "FailureReason=" <> failureReason,
        "CompletedStages=" <> ToString[completedStageCount] <> "/" <> ToString[expectedStageCount],
        If[stderrTail =!= "", "StderrTail=" <> stderrTail, Nothing],
        If[stdoutTail =!= "", "StdoutTail=" <> stdoutTail, Nothing]
      },
      Nothing
    ],
    " | "
  ]
];


ClearAll[SavedBetheRootsCSVRows];
SavedBetheRootsCSVRows[result_Association] := Module[
  {
    runEnvironment, runID, tableau, youngDiagram, succeededQ,
    failureReason, timedResult, timingSeconds, betheRoots,
    diagnostic
  },
  runEnvironment = Lookup[result, "RunEnvironment", <||>];
  runID = Lookup[runEnvironment, "RunID", ""];
  tableau = Lookup[result, "Tableau", Missing["NotAvailable"]];
  youngDiagram = Lookup[result, "YoungDiagram", Missing["NotAvailable"]];
  succeededQ = TrueQ[Lookup[result, "SucceededQ", False]];
  failureReason = Lookup[result, "FailureReason", None];
  timedResult = Lookup[result, "TimedResult", Missing["NotAvailable"]];
  timingSeconds = Replace[
    timedResult,
    {
      values_List /; Length[values] >= 1 :> First[values],
      other_ :> other
    }
  ];
  betheRoots = SavedBetheRootsPayload[result];
  diagnostic = Lookup[result, "Diagnostic", ""];

  {
    {
      "RunID",
      "Tableau",
      "YoungDiagram",
      "SucceededQ",
      "FailureReason",
      "Diagnostic",
      "TimingSeconds",
      "BetheRoots"
    },
    {
      ToString[runID],
      ToString[tableau, InputForm],
      ToString[youngDiagram, InputForm],
      succeededQ,
      If[failureReason === None, "None", ToString[failureReason, InputForm]],
      ToString[diagnostic, InputForm],
      Replace[timingSeconds, value_ /; NumericQ[value] :> N[value]],
      ToString[betheRoots, InputForm]
    }
  }
];


ClearAll[SaveBetheRootsSnapshot];
SaveBetheRootsSnapshot[result_Association, resultDirectory_String] := Module[
  {directory, tableau, outputFile},
  directory = EnsureSUSYWBEDirectory[resultDirectory];
  tableau = Lookup[result, "Tableau", {}];
  outputFile = FileNameJoin[{directory, SYTFileName[tableau]}];

  Export[outputFile, SavedBetheRootsCSVRows[result], "CSV"];
  outputFile
];


ClearAll[WorkflowTimingCSVCell];
WorkflowTimingCSVCell[value_] := Which[
  MatchQ[value, _Missing], "",
  value === None, "None",
  value === Null, "",
  StringQ[value], value,
  value === True || value === False, value,
  NumberQ[value], N[value],
  True, ToString[value, InputForm]
];


ClearAll[WorkflowTimingPrefixedAssociation];
ClearAll[WorkflowTimingKeyString];
WorkflowTimingKeyString[key_String] := key;
WorkflowTimingKeyString[key_] := ToString[key, InputForm];

WorkflowTimingPrefixedAssociation[prefix_String, data_Association] := Association@
  KeyValueMap[
    StringJoin[prefix, WorkflowTimingKeyString[#1]] -> #2 &,
    data
  ];


ClearAll[WorkflowTimingTableauKey];
WorkflowTimingTableauKey[tableau_] := ToString[tableau, InputForm];


ClearAll[BuildDerivedWorkflowStageTimings];
BuildDerivedWorkflowStageTimings[result_Association] := Module[
  {tableau, solutionHistory, subTableaux, usableLength},
  tableau = Lookup[result, "Tableau", {}];
  solutionHistory = Lookup[result, "SolutionHistory", {}];
  subTableaux = Quiet@Check[SYTlist[tableau], {}];
  usableLength = Min[Length[subTableaux], Length[solutionHistory]];

  Table[
    Module[{currentTableau, previousTableau},
      currentTableau = subTableaux[[k]];
      previousTableau = If[k > 1, subTableaux[[k - 1]], Missing["NotApplicable"]];

      <|
        "Stage" -> If[k == 1, "Start", "Interim"],
        "Tableau" -> currentTableau,
        "PreviousTableau" -> previousTableau,
        "YoungDiagram" -> ToYD[currentTableau],
        "PreviousYoungDiagram" -> If[k > 1, ToYD[previousTableau], Missing["NotApplicable"]],
        "WorkflowTimingMeasuredQ" -> False
      |>
    ],
    {k, usableLength}
  ]
];


ClearAll[BuildSolutionHistoryStageData];
BuildSolutionHistoryStageData[result_Association] := Module[
  {tableau, solutionHistory, subTableaux, usableLength},
  tableau = Lookup[result, "Tableau", {}];
  solutionHistory = Lookup[result, "SolutionHistory", {}];
  subTableaux = Quiet@Check[SYTlist[tableau], {}];
  usableLength = Min[Length[subTableaux], Length[solutionHistory]];

  Association@Table[
    Module[{currentTableau, solutionEntry, lambdaValues, coefficientSolution},
      currentTableau = subTableaux[[k]];
      solutionEntry = solutionHistory[[k]];
      lambdaValues = Replace[solutionEntry, {values_List /; Length[values] >= 1 :> values[[1]], _ :> {}}];
      coefficientSolution = Replace[solutionEntry, {values_List /; Length[values] >= 3 :> values[[3]], _ :> {}}];

      WorkflowTimingTableauKey[currentTableau] -> <|
        "SolutionStageIndex" -> k,
        "LambdaSampleCount" -> Length[lambdaValues],
        "FinalLambda" -> If[ListQ[lambdaValues] && lambdaValues =!= {}, Last[lambdaValues], Missing["NotAvailable"]],
        "CoefficientRuleCount" -> If[ListQ[coefficientSolution], Length[coefficientSolution], Missing["NotAvailable"]]
      |>
    ],
    {k, usableLength}
  ]
];


ClearAll[BuildWorkflowTimingRows];
BuildWorkflowTimingRows[result_Association] := Module[
  {
    runEnvironment, configuration, timedResult, totalSeconds, workflowStageTimings,
    juliaStageTimings, workflowRows, summaryRow, expectedStageCount,
    completedStageCount, solutionHistoryStageData, juliaByTableau,
    matchedJuliaKeys, topLevelMetadata, configurationMetadata, stageCounter = 0,
    unmatchedJuliaRows
  },
  runEnvironment = Lookup[result, "RunEnvironment", <||>];
  configuration = Lookup[result, "Configuration", <||>];
  timedResult = Lookup[result, "TimedResult", Missing["NotAvailable"]];
  totalSeconds = Replace[
    timedResult,
    {
      values_List /; Length[values] >= 1 :> First[values],
      other_ :> other
    }
  ];
  workflowStageTimings = Lookup[result, "WorkflowStageTimings", {}];
  juliaStageTimings = Lookup[result, "JuliaStageTimings", {}];
  expectedStageCount = Quiet@Check[Length[SYTlist[Lookup[result, "Tableau", {}]]], Missing["NotAvailable"]];
  completedStageCount = Length[Lookup[result, "SolutionHistory", {}]];
  solutionHistoryStageData = BuildSolutionHistoryStageData[result];
  juliaByTableau = GroupBy[
    Select[juliaStageTimings, AssociationQ],
    WorkflowTimingTableauKey[Lookup[#, "TableauStep", Missing["NotAvailable"]]] &
  ];
  matchedJuliaKeys = <||>;

  topLevelMetadata = <|
    "RecordType" -> "RunSummary",
    "RunID" -> Lookup[runEnvironment, "RunID", ""],
    "FinalTableau" -> Lookup[result, "Tableau", Missing["NotAvailable"]],
    "FinalYoungDiagram" -> Lookup[result, "YoungDiagram", Missing["NotAvailable"]],
    "SucceededQ" -> TrueQ[Lookup[result, "SucceededQ", False]],
    "FailureReason" -> Lookup[result, "FailureReason", None],
    "TotalRunSeconds" -> totalSeconds,
    "ExpectedStageCount" -> expectedStageCount,
    "CompletedStageCount" -> completedStageCount
  |>;
  configurationMetadata = WorkflowTimingPrefixedAssociation["Configuration/", configuration];
  topLevelMetadata = Join[
    topLevelMetadata,
    WorkflowTimingPrefixedAssociation["RunEnvironment/", runEnvironment],
    configurationMetadata
  ];

  workflowStageTimings = If[
    ListQ[workflowStageTimings] && workflowStageTimings =!= {},
    workflowStageTimings,
    BuildDerivedWorkflowStageTimings[result]
  ];

  summaryRow = Join[
    topLevelMetadata,
    <|
      "StageIndex" -> 0,
      "Stage" -> "RunSummary",
      "JuliaStageCount" -> Length[juliaStageTimings],
      "WorkflowStageCount" -> Length[workflowStageTimings]
    |>
  ];

  workflowRows = Map[
    Function[stageData,
      Module[
        {
          row, stageTableau, stageTableauKey, stageSolutionData,
          matchingJuliaRows, firstJuliaRow, stageName
        },
        stageCounter += 1;
        stageName = Lookup[stageData, "Stage", ""];
        stageTableau = Lookup[stageData, "Tableau", Missing["NotAvailable"]];
        stageTableauKey = WorkflowTimingTableauKey[stageTableau];
        stageSolutionData = If[
          MemberQ[{"Start", "Interim"}, stageName],
          Lookup[solutionHistoryStageData, stageTableauKey, <||>],
          <||>
        ];
        matchingJuliaRows = If[
          stageName === "Interim",
          Lookup[juliaByTableau, stageTableauKey, {}],
          {}
        ];
        If[matchingJuliaRows =!= {}, matchedJuliaKeys[stageTableauKey] = True];
        firstJuliaRow = If[matchingJuliaRows === {}, <||>, First[matchingJuliaRows]];

        row = Join[
          topLevelMetadata,
          <|"RecordType" -> "Stage", "StageIndex" -> stageCounter|>,
          stageData,
          stageSolutionData,
          If[
            firstJuliaRow === <||>,
            <|"JuliaTimingAvailableQ" -> False|>,
            Join[
              <|"JuliaTimingAvailableQ" -> True|>,
              WorkflowTimingPrefixedAssociation["Julia/", firstJuliaRow]
            ]
          ]
        ];

        row
      ]
    ],
    Select[workflowStageTimings, AssociationQ]
  ];

  unmatchedJuliaRows = Map[
    Function[juliaRow,
      Join[
        topLevelMetadata,
        <|
          "RecordType" -> "JuliaOnly",
          "StageIndex" -> Missing["NotAvailable"],
          "Stage" -> "JuliaOnly",
          "JuliaTimingAvailableQ" -> True
        |>,
        WorkflowTimingPrefixedAssociation["Julia/", juliaRow]
      ]
    ],
    Select[
      juliaStageTimings,
      AssociationQ[#] && ! TrueQ[Lookup[matchedJuliaKeys, WorkflowTimingTableauKey[Lookup[#, "TableauStep", Missing["NotAvailable"]]], False]] &
    ]
  ];

  Join[{summaryRow}, workflowRows, unmatchedJuliaRows]
];


ClearAll[WorkflowTimingCSVRows];
WorkflowTimingCSVRows[result_Association] := Module[
  {rowAssociations, preferredColumns, allColumns},
  rowAssociations = BuildWorkflowTimingRows[result];
  preferredColumns = {
    "RecordType",
    "RunID",
    "SucceededQ",
    "FailureReason",
    "TotalRunSeconds",
    "ExpectedStageCount",
    "CompletedStageCount",
    "StageIndex",
    "Stage",
    "FinalTableau",
    "FinalYoungDiagram",
    "Tableau",
    "YoungDiagram",
    "PreviousTableau",
    "PreviousYoungDiagram",
    "LambdaSampleCount",
    "FinalLambda",
    "CoefficientRuleCount",
    "WorkflowTimingMeasuredQ",
    "JuliaTimingAvailableQ"
  };
  allColumns = Join[
    Select[preferredColumns, MemberQ[Union @@ (Keys /@ rowAssociations), #] &],
    Sort@Complement[Union @@ (Keys /@ rowAssociations), preferredColumns]
  ];

  Join[
    {allColumns},
    Map[
      WorkflowTimingCSVCell /@ Lookup[#, allColumns, Missing["NotAvailable"]] &,
      rowAssociations
    ]
  ]
];


ClearAll[SaveWorkflowTimingSnapshot];
SaveWorkflowTimingSnapshot[result_Association, workflowTimingFile_String] := Module[
  {outputFile},
  outputFile = ExpandFileName[workflowTimingFile];
  If[
    ! DirectoryQ[DirectoryName[outputFile]],
    CreateDirectory[DirectoryName[outputFile], CreateIntermediateDirectories -> True]
  ];

  Export[outputFile, WorkflowTimingCSVRows[result], "CSV"];
  outputFile
];


Options[RunSingleSYT] = Join[
  Options[SetSingleSYTRunConfiguration],
  Options[BuildSYTRunEnvironment],
  {
    MuteProgress -> False,
    SaveBetheRootsBySYT -> False,
    SaveWorkflowTimingCSV -> False,
    ResultSYTDirectory -> Automatic,
    CollectRunResults -> True
  }
];

RunSingleSYT[tableau_List, opts : OptionsPattern[]] := Module[
  {
    baseConfiguration, configurationRules, runEnvironment, cleanupWorkDir,
    timedResult, solutionHistory, youngDiagram, result, startTime,
    betheRoots, succeededQ, failureReason, muteProgress,
    saveBetheRootsBySYT, saveWorkflowTimingCSV, resultSYTDirectory,
    betheRootsFile, workflowTimingFile
  },
  baseConfiguration = GetSingleSYTRunConfiguration[];
  configurationRules = FilterRules[{opts}, Options[SetSingleSYTRunConfiguration]];
  muteProgress = TrueQ[OptionValue[MuteProgress]];
  saveBetheRootsBySYT = TrueQ[OptionValue[SaveBetheRootsBySYT]];
  saveWorkflowTimingCSV = TrueQ[OptionValue[SaveWorkflowTimingCSV]];
  resultSYTDirectory = Replace[
    OptionValue[ResultSYTDirectory],
    Automatic :> DefaultResultSYTDirectory[]
  ];
  runEnvironment = BuildSYTRunEnvironment[
    Sequence @@ FilterRules[{opts}, Options[BuildSYTRunEnvironment]]
  ];
  cleanupWorkDir = runEnvironment["CleanupWorkDir"];

  result = Block[
    {
      $SUSYWBEMuteProgress = muteProgress,
      $SUSYWBEJuliaRunConfiguration = runEnvironment,
      $SUSYWBECurrentRunConfiguration,
      \[CapitalLambda]0Interim,
      \[CapitalLambda]target,
      startinterpord,
      prec,
      interpord,
      $CurrentIterator,
      ansWprov,
      Steps,
      StepsStepwise,
      ansWholeIteration,
      predictorCorrectorList,
      currentsol,
      \[CapitalLambda]vals,
      interstep,
      MYminsolrep,
      minsolrep,
      step,
      savedJuliaTime,
      savedWorkflowStageTime
    },
    configuration = SetSingleSYTRunConfiguration @@ Replace[
      configurationRules,
      {} :> Normal[baseConfiguration]
    ];

    savedJuliaTime = {};
    savedWorkflowStageTime = {};
    startTime = AbsoluteTime[];
    solutionHistory = BlockRandom[
      SeedRandom[Hash[HoldForm[tableau], "SHA256"]];
      ansWprov = SolutionFromSYTUptdStepwiseWronskian[tableau]
    ];
    timedResult = {AbsoluteTime[] - startTime, solutionHistory};
    youngDiagram = ToYD[tableau];
    succeededQ = ValidSolutionHistoryQ[solutionHistory];
    failureReason = If[succeededQ, None, "Solver returned no solution history"];
    betheRoots = If[
      succeededQ,
      ExtractBetheRootsFromSolutionHistory[solutionHistory, youngDiagram],
      Missing["SolverFailed", failureReason]
    ];

    <|
      "Configuration" -> configuration,
      "RunEnvironment" -> runEnvironment,
      "Tableau" -> tableau,
      "YoungDiagram" -> youngDiagram,
      "TimedResult" -> timedResult,
      "WorkflowStageTimings" -> savedWorkflowStageTime,
      "JuliaStageTimings" -> savedJuliaTime,
      "SucceededQ" -> succeededQ,
      "FailureReason" -> failureReason,
      "SolutionHistory" -> solutionHistory,
      "BetheRoots" -> betheRoots
    |>
  ];

  result = Append[result, "Diagnostic" -> BuildRunFailureDiagnostic[result]];
  betheRootsFile = If[
    saveBetheRootsBySYT,
    Quiet@Check[
      SaveBetheRootsSnapshot[result, resultSYTDirectory],
      Missing["SaveFailed", resultSYTDirectory]
    ],
    Missing["NotSaved"]
  ];
  result = Append[result, "BetheRootsFile" -> betheRootsFile];
  workflowTimingFile = If[
    saveWorkflowTimingCSV,
    Quiet@Check[
      SaveWorkflowTimingSnapshot[result, Lookup[runEnvironment, "WorkflowTimingFile", FileNameJoin[{runEnvironment["WorkDir"], "workflow.timings.csv"}]]],
      Missing["SaveFailed", Lookup[runEnvironment, "WorkflowTimingFile", Missing["NotConfigured"]]]
    ],
    Missing["NotSaved"]
  ];
  result = Append[result, "WorkflowTimingFile" -> workflowTimingFile];

  If[
    cleanupWorkDir && DirectoryQ[runEnvironment["WorkDir"]],
    Quiet@DeleteDirectory[runEnvironment["WorkDir"], DeleteContents -> True]
  ];

  result
];


RunSingleSYTSafe[tableau_List, opts : OptionsPattern[RunSingleSYT]] :=
  RunSingleSYT[tableau, opts];


RunAllSYTSerial[input_List, opts : OptionsPattern[RunSingleSYT]] := Module[
  {tableaux, runResults, timing, baseOptions, baseRunEnvironmentRules, behaviorRules},
  tableaux = ResolveTableauxInput[input];
  baseOptions = {opts};
  behaviorRules = FilterRules[baseOptions, {MuteProgress, SaveBetheRootsBySYT, SaveWorkflowTimingCSV, ResultSYTDirectory}];
  baseRunEnvironmentRules = FilterRules[baseOptions, {CleanupWorkDir, JuliaBackend, JuliaTimeout, JuliaProcessFlags, JuliaSysimagePath, JuliaExecutable, SaveSubSYTCSVFiles, WorkflowTimingFile}];
  timing = AbsoluteTiming[
    runResults = MapIndexed[
      RunSingleSYTSafe[
        #1,
        Sequence @@ FilterRules[baseOptions, Options[SetSingleSYTRunConfiguration]],
        Sequence @@ behaviorRules,
        Sequence @@ BuildTaskScopedRunOptions[First[#2], #1, baseOptions]
        ,
        Sequence @@ baseRunEnvironmentRules
      ] &,
      tableaux
    ];
  ];

  <|
    "Tableaux" -> tableaux,
    "RunResults" -> runResults,
    "BetheRoots" -> runResults[[All, "BetheRoots"]],
    "BetheRootsFiles" -> Lookup[runResults, "BetheRootsFile", Missing["NotSaved"]],
    "WorkflowTimingFiles" -> Lookup[runResults, "WorkflowTimingFile", Missing["NotSaved"]],
    "Timing" -> First[timing]
  |>
];


RunAllSYTParallel[input_List, opts : OptionsPattern[RunSingleSYT]] := Module[
  {
    tableaux, runResults, timing, workflowFile, baseOptions,
    configurationRules, behaviorRules, runEnvironmentRules, effectiveRunEnvironmentRules,
    indexedTasks, collectRunResults
  },
  tableaux = ResolveTableauxInput[input];
  workflowFile = FileNameJoin[{SUSYWBEProjectDirectory[], "SUSYWBEWorkflow.wl"}];
  baseOptions = {opts};
  collectRunResults = ! FalseQ[Replace[CollectRunResults /. baseOptions, CollectRunResults -> True]];
  configurationRules = FilterRules[baseOptions, Options[SetSingleSYTRunConfiguration]];
  behaviorRules = FilterRules[baseOptions, {MuteProgress, SaveBetheRootsBySYT, SaveWorkflowTimingCSV, ResultSYTDirectory}];
  runEnvironmentRules = FilterRules[baseOptions, {CleanupWorkDir, JuliaBackend, JuliaTimeout, JuliaProcessFlags, JuliaSysimagePath, JuliaExecutable, SaveSubSYTCSVFiles, WorkflowTimingFile}];
  effectiveRunEnvironmentRules = If[
    MatchQ[runEnvironmentRules, {___, JuliaBackend -> _, ___}],
    runEnvironmentRules,
    Append[runEnvironmentRules, JuliaBackend -> "ProcessPerRun"]
  ];
  indexedTasks = MapIndexed[
    <|
      "Index" -> First[#2],
      "Tableau" -> #1,
      "TaskOptions" -> BuildTaskScopedRunOptions[First[#2], #1, baseOptions]
    |>&,
    tableaux
  ];

  If[Kernels[] === {}, LaunchKernels[]];
  ParallelEvaluate[Get[workflowFile]];
  ParallelEvaluate[Off[FrontEndObject::notavail]];
  DistributeDefinitions[configurationRules, behaviorRules, effectiveRunEnvironmentRules, mPfunction];

  runResults = {};
  timing = AbsoluteTiming[
    If[collectRunResults,
      runResults = ParallelMap[
        Function[{task},
          Module[{tableau, taskOptions},
            tableau = task["Tableau"];
            taskOptions = task["TaskOptions"];
            RunSingleSYTSafe[
              tableau,
              Sequence @@ configurationRules,
              Sequence @@ behaviorRules,
              Sequence @@ taskOptions,
              Sequence @@ effectiveRunEnvironmentRules
            ]
          ]
        ],
        indexedTasks
      ],
      ParallelDo[
        Module[{tableau, taskOptions},
          tableau = task["Tableau"];
          taskOptions = task["TaskOptions"];
          RunSingleSYTSafe[
            tableau,
            Sequence @@ configurationRules,
            Sequence @@ behaviorRules,
            Sequence @@ taskOptions,
            Sequence @@ effectiveRunEnvironmentRules
          ];
        ],
        {task, indexedTasks}
      ]
    ];
  ];

  <|
    "Tableaux" -> tableaux,
    "RunResults" -> runResults,
    "BetheRoots" -> If[collectRunResults, runResults[[All, "BetheRoots"]], {}],
    "BetheRootsFiles" -> If[collectRunResults, Lookup[runResults, "BetheRootsFile", Missing["NotSaved"]], {}],
    "WorkflowTimingFiles" -> If[collectRunResults, Lookup[runResults, "WorkflowTimingFile", Missing["NotSaved"]], {}],
    "CollectRunResults" -> collectRunResults,
    "Timing" -> First[timing]
  |>
];


singleSYTresultUNIK[tableau_List] := Module[{configuration},
  configuration = GetSingleSYTRunConfiguration[];

  SetSingleSYTRunConfiguration[
    InitialLambda -> 20,
    TargetLambda -> 0,
    StartInterpolationOrder -> 2,
    WorkingPrecision -> 40,
    InterpolationOrder -> 3,
    IteratorFunction -> configuration[IteratorFunction]
  ];

  ansWprov = SolutionFromSYTUptdStepwiseWronskian[tableau]
];


ExtractBetheRootsFromCoefficients[yd_List, coefficientSolutions_] := Module[
  {solutionList, bethePolynomials},
  solutionList = If[
    MatchQ[coefficientSolutions, {(_Rule) ..}],
    {coefficientSolutions},
    coefficientSolutions
  ];

  Map[
    Function[coefficientSolution,
      bethePolynomials = Table[YQa[level, 0, yd], {level, Length[yd] - 1}] /. coefficientSolution;
      Map[
        Function[polynomial,
          Module[{roots = Solve[polynomial == 0, u]},
            If[roots === {}, Missing["NoSolution"], u /. roots]
          ]
        ],
        bethePolynomials
      ]
    ],
    solutionList
  ]
][[1]];


ExtractBetheRootsFromSolutionHistory[solutionHistory_, yd_List] :=
  If[
    ValidSolutionHistoryQ[solutionHistory],
    ExtractBetheRootsFromCoefficients[yd, Last[Last[solutionHistory]]],
    Missing["SolverFailed", "No solution history available"]
  ];


ClearAll[ValidSolutionHistoryQ];
ValidSolutionHistoryQ[solutionHistory_] := MatchQ[
  solutionHistory,
  {
    ___,
    {_, _, _}
  }
];


ClearAll[NormalizeBetheRoots];
NormalizeBetheRoots[data_, tolerance_: 10^-18] := Module[{normalize},
  normalize[value_?NumericQ] := Chop[N[value, 50], tolerance];
  normalize[list_List] := Module[{normalizedList = normalize /@ list},
    If[
      VectorQ[normalizedList, NumericQ],
      SortBy[normalizedList, {Re[#] &, Im[#] &}],
      normalizedList
    ]
  ];
  normalize[data]
];


ClearAll[MaxBetheRootDifference];
MaxBetheRootDifference[left_, right_, tolerance_: 10^-18] := Module[
  {normalizedLeft, normalizedRight, leftValues, rightValues},
  normalizedLeft = NormalizeBetheRoots[left, tolerance];
  normalizedRight = NormalizeBetheRoots[right, tolerance];

  leftValues = Cases[normalizedLeft, _?NumericQ, Infinity];
  rightValues = Cases[normalizedRight, _?NumericQ, Infinity];

  If[
    normalizedLeft === normalizedRight,
    0,
    If[
      Length[leftValues] =!= Length[rightValues] || Dimensions[normalizedLeft] =!= Dimensions[normalizedRight],
      Infinity,
      Max[Abs[N[leftValues - rightValues, 50]]]
    ]
  ]
];


ClearAll[BetheRootsEquivalentQ];
BetheRootsEquivalentQ[left_, right_, tolerance_: 10^-18] :=
  MaxBetheRootDifference[left, right, tolerance] <= tolerance;


ClearAll[ValidateSYTRunResults];
ValidateSYTRunResults[
  serialRun_Association,
  parallelRun_Association,
  reference_: Automatic,
  tolerance_: 10^-18
] := Module[
  {
    serialRoots, parallelRoots, referenceRoots,
    serialParallelDifference, parallelReferenceDifference
  },
  serialRoots = serialRun["BetheRoots"];
  parallelRoots = parallelRun["BetheRoots"];
  referenceRoots = Replace[reference, Automatic :> Missing["NotProvided"]];

  serialParallelDifference = MaxBetheRootDifference[serialRoots, parallelRoots, tolerance];
  parallelReferenceDifference = If[
    referenceRoots === Missing["NotProvided"],
    Missing["NotProvided"],
    MaxBetheRootDifference[parallelRoots, referenceRoots, tolerance]
  ];

  <|
    "NumberOfTableaux" -> Length[serialRun["Tableaux"]],
    "SerialParallelMatchQ" -> BetheRootsEquivalentQ[serialRoots, parallelRoots, tolerance],
    "ParallelReferenceMatchQ" -> If[
      referenceRoots === Missing["NotProvided"],
      Missing["NotProvided"],
      BetheRootsEquivalentQ[parallelRoots, referenceRoots, tolerance]
    ],
    "SerialParallelMaxDifference" -> serialParallelDifference,
    "ParallelReferenceMaxDifference" -> parallelReferenceDifference,
    "Tolerance" -> tolerance,
    "SerialTiming" -> serialRun["Timing"],
    "ParallelTiming" -> parallelRun["Timing"],
    "TimingRatioSerialOverParallel" -> If[parallelRun["Timing"] == 0, Infinity, serialRun["Timing"]/parallelRun["Timing"]]
  |>
];


GetMarkedPointSelector[];
GetSingleSYTRunConfiguration[];
