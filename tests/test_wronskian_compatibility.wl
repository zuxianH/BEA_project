(* Run with WolframKernel -noprompt -script tests/test_wronskian_compatibility.wl *)
project = DirectoryName[DirectoryName[$InputFileName]];
Off[FrontEndObject::notavail];
assert[condition_, label_] := If[! TrueQ[condition], Print["FAIL: ", label]; Exit[1]];
loaded = Check[Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]]; True, False];
assert[loaded, "solver loads without errors"];

(* Check bosonic, diagonal, and both orientations of mixed marked points. *)
Do[
  yd = {4, 2, 1};
  wronskian = GenerateSusyWronskian[point, yd]["SusyWronskian"];
  assert[! ListQ[wronskian] && PolynomialQ[wronskian, u], "Wronskian remains a polynomial"];
  assert[Exponent[wronskian, u] == Total[yd], "Wronskian degree"];
  SetMarkedPointSelector[Function[diagram, point]];
  system = Check[BuildSUSYWSystemData[yd], $Failed];
  assert[AssociationQ[system], "system builds without errors"];
  forward = system["SusyToCCoefficients"];
  backward = system["CToSusyCoefficients"];
  assert[MatchQ[forward, {__Rule}] && MatchQ[backward, {__Rule}], "coefficient conversions return rules"];
  variables = system["SusyVariables"];
  assert[Length[variables] == Total[yd], "all SUSY variables retained"];
  assert[Sort[First /@ forward] === Sort[variables], "all SUSY coefficients have conversion rules"];
  assert[Complement[Variables[Last /@ backward], variables] === {},
    "C coefficients depend only on independent SUSY coefficients"];
  symRules = Table[sym[k] -> Coefficient[Getmonic[wronskian], u, Total[yd] - k], {k, Total[yd]}];
  assert[AllTrue[Simplify[(variables /. forward /. backward /. symRules) - variables], # === 0 &],
    "SUSY coefficients survive a consistent round trip"];
  Print["PASS: ", yd, " at ", point];
  , {point, {{3, 0}, {2, 1}, {2, 2}, {1, 2}}}
];
Print["All Wronskian compatibility checks passed."];
Exit[0];
