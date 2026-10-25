(* Run with WolframKernel -noprompt -script tests/test_continuation_export.wl *)
project = DirectoryName[DirectoryName[$InputFileName]];
Off[FrontEndObject::notavail];
Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]];
assert[condition_, label_] := If[! TrueQ[condition], Print["FAIL: ", label]; Exit[1]];
scratch = CreateDirectory[];
csv = FileNameJoin[{scratch, "initial_data.csv"}];
Block[{InterpEqnsUptd, MyFindRoot, susyvars = {x, y}, MYminsolrep = {y -> 22, x -> 11},
    prec = 80, \[CapitalLambda]0 = 500,
    $SUSYWBEJuliaRunConfiguration = <|"SavedDataDir" -> scratch, "InitialDataFile" -> csv,
      "SaveSubSYTCSVFiles" -> False|>},
  InterpEqnsUptd[_] := {x - 11, y - 22};
  MyFindRoot := Null;
  exportToJuliaInitialData[{{1, 2}}, False];
];
rows = Import[csv, "CSV"];
assert[rows[[2 ;;, 3]] === {"x", "y"}, "export keeps the declared variable order"];
assert[ToExpression /@ rows[[2 ;;, 4]] == {11, 22},
  "initial values match their variables even when solution rules are reordered"];
DeleteDirectory[scratch, DeleteContents -> True];
Print["All continuation export checks passed."];
Exit[0];
