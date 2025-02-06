(* ::Package:: *)

BeginPackage["MyPackage`"]

(* Declare function usage messages *)
log::usage = "log[z, branch:0, branchcut:-Pi] computes the logarithm with a custom branch and branch cut.";
arg::usage = "arg[z, branch:0, branchcut:-Pi] computes the argument with a specified branch and branch cut.";
F::usage = "F[u, branch:0, branchcut:-Pi] computes the function (-1/(2Pi*I)) * log[(u+I)/(u-I)] with branch parameters.";
Fsym::usage = "Fsym[u, branch:0, branchcut:-Pi] computes a symmetric version of F, subtracting 1/2.";

Mset::usage = "Mset[magnon] computes all possible \!\(\*SubscriptBox[\(M\), \(s\)]\) sets;the index is the string length and the value is the number of strings of that length";
replaceMset::usage = "return a list that place \!\(\*SubscriptBox[\(M\), \(s\)]\)->value";
stringsets::usage ="All possible stringvectors; the entries are the strings, with values corresponding to the length of these strings; stringsets[[i]]==length of string i";


(* Declare global symbols that should be accessible outside `Private` *)



Begin["`Private`"]
M;
(* Define basic function *)
log[z_,branch_:0,branchcut_:-Pi]:=Log[Abs[z]]+I*(Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi+2Pi*branch); (*Some initial definitions.*)
arg[z_,branch_:0,branchcut_:-Pi]:=Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi
F[u_,branch_:0,branchcut_:-Pi]:=(-1/(2Pi*I))log[(u+I)/(u-I),branch,branchcut];
Fsym[u_,branch_:0,branchcut_:-Pi]:=F[u,branch,branchcut]-1/2;

Mset[M_]:=Values[Solve[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(s = 1\), \(M\)]\(s\ MM[s]\)\)==M,Table[MM[t],{t,1,M}],NonNegativeIntegers]];
replaceMset[magnon_]:=Table[Thread[Subscript[M,#]->Mset[magnon][[k]][[#]]&/@Range[Length[Mset[magnon][[k]]]]],{k,Length[Mset[magnon]]}]
stringsets[M_]:=Table[Catenate[ Table[Table[i,{j,set[[i]]}],{i,Length[set]}]],{set,Mset[M]}];

End[]
EndPackage[]




