(* Run with WolframKernel -noprompt -script tests/test_marked_point_selector.wl *)
project = DirectoryName[DirectoryName[$InputFileName]];
Off[FrontEndObject::notavail];
Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]];
assert[condition_, label_] := If[!TrueQ[condition], Print["FAIL: ", label]; Exit[1]];

assert[GetMarkedPointSelector[] === UseDiagonalMarkedPoint, "fresh workflows default to diagonal selection"];
Do[
  point = UseDiagonalMarkedPoint[yd];
  boundary = Endpoints[yd];
  assert[MemberQ[boundary, point], "selected point lies on the diagram boundary"];
  assert[point[[1]] === point[[2]], "selected point is diagonal"];
  assert[Max[point] === Min[Max /@ boundary], "selected point minimizes permutation rank"];
  , {n, 1, 8}, {yd, IntegerPartitions[n]}
];
assert[UseDiagonalMarkedPoint[{4, 2, 1}] === {2, 2}, "seven-box choice"];
assert[UseDiagonalMarkedPoint[{9, 4, 3, 2, 1}] === {3, 3}, "nineteen-box choice"];
SetMarkedPointSelector[UseLeftmostBosonicMarkedPoint];
assert[mPfunction[{4, 2, 1}] === {3, 0}, "explicit bosonic selection remains available"];
SetMarkedPointSelector[];
Do[
  system = Check[BuildSUSYWSystemData[yd], $Failed];
  assert[AssociationQ[system], "default setup succeeds on small growing shapes"];
  assert[system["MarkedPoint"] === UseDiagonalMarkedPoint[yd], "setup uses current shape"];
  assert[Length[system["SusyVariables"]] === Total[yd], "all independent variables retained"];
  , {yd, {{2, 1}, {2, 2}, {4, 2, 1}}}
];
Print["All default marked-point checks passed."];
Exit[0];
