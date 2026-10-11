(* Run with WolframKernel -noprompt -script tests/test_terminal_progress.wl *)
project = DirectoryName[DirectoryName[$InputFileName]];
Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]];
assert[condition_, label_] := If[! TrueQ[condition], Print["FAIL: ", label]; Exit[1]];

assert[SUSYWBETableauText[{{1, 3}, {2}}] ===
  "+---+---+\n| 1 | 3 |\n+---+---+\n| 2 |\n+---+", "ragged tableau text"];
wide = SUSYWBETableauText[{Range[10]}];
assert[StringContainsQ[wide, "| 9  | 10 |"], "multi-digit alignment"];

evaluations = 0;
SetEnvironment["BAE_STUDIO_TERMINAL" -> "0"];
SUSYWBEStagePrint[evaluations++];
assert[evaluations == 0, "terminal disabled remains unevaluated"];
SetEnvironment["BAE_STUDIO_TERMINAL" -> "1"];
Block[{$SUSYWBEMuteProgress = True}, SUSYWBEStagePrint[evaluations++]];
assert[evaluations == 1, "stage output works while numerical diagnostics are muted"];
Print["All terminal progress checks passed."];
Exit[0];
