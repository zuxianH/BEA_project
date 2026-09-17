(* Run from any working directory; checks canonical source and output paths. *)
project = DirectoryName[DirectoryName[$InputFileName]];
assert[condition_, label_] := If[! TrueQ[condition], Print["FAIL: ", label]; Exit[1]];
Get[FileNameJoin[{project, "wolfram", "SUSYWBEWorkflow.wl"}]];
assert[SUSYWBEProjectDirectory[] === project, "workflow finds project root"];
assert[SUSYWBESolverDirectory[] === FileNameJoin[{project, "wolfram", "solver"}], "canonical solver path"];
assert[SUSYWBEUtilsDirectory[] === FileNameJoin[{project, "wolfram", "utils"}], "canonical utility path"];
assert[DefaultResultSYTDirectory[] === FileNameJoin[{project, "workspace", "results"}], "generated result path"];
Get[FileNameJoin[{project, "wolfram", "checkDistances.wl"}]];
assert[$CheckDistancesDirectory === FileNameJoin[{project, "data", "references"}], "reference directory has no user-specific path"];
Print["All Wolfram path checks passed."];
Exit[0];
