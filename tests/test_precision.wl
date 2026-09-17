(* Run with WolframKernel -noprompt -script tests/test_precision.wl *)
project = DirectoryName[DirectoryName[$InputFileName]];
Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]];
assert[condition_, label_] := If[! TrueQ[condition], Print["FAIL: ", label]; Exit[1]];

decimal = "-1.261916638205475269217559470625363788963271241884296883585713688115164877170678168670991633845213071100e+00";
expected = -1261916638205475269217559470625363788963271241884296883585713688115164877170678168670991633845213071100/10^102;
value = ParseContinuationReal[decimal, 100];
assert[Precision[value] >= 99, "100-digit decimal precision"];
assert[Abs[value - expected] < 10^-99, "digits preserved before numeric conversion"];
assert[ParseContinuationReal[".125E+2", 100] == 25/2, "leading decimal/exponent"];
assert[ParseContinuationReal["-2.5*^-3", 100] == -1/400, "Wolfram exponent"];
assert[ParseContinuationReal["7.", 100] == 7, "trailing decimal"];
assert[ParseContinuationReal["0e-99", 100] == 0, "zero"];
assert[ParseContinuationReal["1;Quit[]", 100] === $Failed, "reject expression"];
assert[ParseContinuationReal["NaN", 100] === $Failed, "reject non-finite value"];

scratch = CreateDirectory[];
csv = FileNameJoin[{scratch, "output.csv"}];
Export[csv, {{"var", "b_final_value"}, {"x", decimal}}, "CSV"];
Block[{$SUSYWBEJuliaRunConfiguration = <|"OutputFile" -> csv|>, prec = 100},
  imported = ReadJuliaResultVector[];
  assert[Length[imported] == 1 && Abs[First[imported] - expected] < 10^-99, "CSV precision round trip"];
  Export[csv, {{"var", "b_final_value"}, {"x", "bad"}}, "CSV"];
  assert[ReadJuliaResultVector[] === $Failed, "malformed output rejected"];
];
DeleteDirectory[scratch, DeleteContents -> True];

evaluations = 0;
Block[{$SUSYWBEMuteProgress = True}, SUSYWBEProgressPrint[evaluations++]];
assert[evaluations == 0, "muted diagnostic remains unevaluated"];
Block[{$SUSYWBEMuteProgress = False}, SUSYWBEProgressPrint[evaluations++]];
assert[evaluations == 1, "enabled diagnostic evaluates once"];
Print["All Wolfram precision and diagnostic checks passed."];
Exit[0];
