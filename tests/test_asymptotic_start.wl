(* Run with WolframKernel -noprompt -script tests/test_asymptotic_start.wl *)
project = DirectoryName[DirectoryName[$InputFileName]];
Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]];
assert[condition_, label_] := If[! TrueQ[condition], Print["FAIL: ", label]; Exit[1]];

(* Exact starting root from the {{1,3},{2}} failure at 200 digits. *)
Block[{normedrel = {-81/40 - 2 x}, vars = {x}, subnc = {x -> -81/80},
       prec = 200, minim, minsolrep},
  FindSolUptdAsymptW;
  assert[minim === 0, "exact residual gives exact minimum"];
  assert[minsolrep === subnc, "exact starting solution retained"];
];

(* A nonzero starting residual must still go through numerical minimization. *)
Block[{normedrel = {x - 2}, vars = {x}, subnc = {x -> 0},
       prec = 80, minim, minsolrep},
  FindSolUptdAsymptW;
  assert[NumericQ[minim] && Abs[(x /. minsolrep) - 2] < 10^-35,
    "nonzero initial residual is minimized"];
];

(* An invalid objective must stop before replacement rules are consumed. *)
Block[{normedrel = {notNumeric[x]}, vars = {x}, subnc = {x -> 0},
       prec = 80, minim, minsolrep},
  failure = Quiet@Catch[FindSolUptdAsymptW];
  assert[failure === $Failed, "failed minimizer terminates the tableau"];
  assert[! ValueQ[minsolrep], "failed minimizer publishes no replacement rules"];
];

Print["All asymptotic starting-solution checks passed."];
Exit[0];
