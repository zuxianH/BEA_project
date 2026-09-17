(* ::Package:: *)

(* ::Subsubsection:: *)
(*Initial equations*)


(* ::Input::Initialization:: *)
(*Some initial definitions.*)

log[z_,branch_:0,branchcut_:-Pi]:=Log[Abs[z]]+I*(Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi+2Pi*branch); 
arg[z_,branch_:0,branchcut_:-Pi]:=Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi;
F[u_,branch_:0,branchcut_:-Pi]:=(-1/(2Pi*I))log[(u+I)/(u-I),branch,branchcut];
Fsym[u_,branch_:0,branchcut_:-Pi]:=F[u,branch,branchcut]-1/2;
Fsym[u_,-1,0]:=(1/Pi)ArcTan[u];

Cartan[a_]:=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{a,a}]
Kernel[s_]:=Array[Min[#1,#2]&,{s,s}]


(* ::Input::Initialization:: *)
(*Importing a Matlab package allowing us to plot rigged configurations*)
(*SetDirectory["../utils"];*)
<<RC.m;
Quiet[Needs["Combinatorica`"]];
ToTableau[path_]:=Block[{pr=path//Flatten,max},max=Max[pr];
Table[Position[pr,k]//Flatten,{k,max}]];
ToSYT[rigged_]:=ToTableau[kkrrec[ConstantArray[{1,1},Length[rigged[[1,1]]]],rigged[[2;;3]]]];
ToCrystalPath[stb_]:=Block[{len=Length[stb//Flatten]},Table[{{Position[stb,k][[1,1]]}},{k,len}]];
ToRigged[SYT_,n_]:=rkkrec[ToCrystalPath[SYT],n];

OrderRiggingsAsc[rc_] := Module[{ans = rc, pairs},
  Do[
    pairs = Transpose[{ans[[2, a]], ans[[3, a]]}];
    (* length descending, then rigging ascending *)
    pairs = SortBy[pairs, {-First[#] &, Last[#] &}];
    ans[[2, a]] = pairs[[All, 1]];
    ans[[3, a]] = pairs[[All, 2]];
  , {a, Length[ans[[2]]]}];
  ans
];
ToRiggedExact[SYT_] := Module[{path, rank, rc},
  path = ToCrystalPath[SYT];
  rank = Max[Flatten[path]];
  rc = rkkrec[path, rank];
  OrderRiggingsAsc[rc]
];


(* ::Input::Initialization:: *)
ModestoRiggedConfig[L_,modes_]:=Module[{Mmatrix,limits},
Mmatrix=PadRight[Append[Prepend[Table[Length[modes[[i,j]]],{i,Length[modes]},{j,Length[modes[[i]]]}],SparseArray[1->L,1]],{0}]];
limits=(Delete[-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[Length[Mmatrix[[1]]]],{{1},{-1}}]+Delete[Mmatrix/.{0->{}},{{1},{-1}}])/2-1/2;
Prepend[Append[{}]/@(Table[{Table[ConstantArray[i,Length[modes[[j,i]]]],{i,Sort[Range[Length[modes[[j]]]],Greater]}]//Catenate,Table[limits[[j,i]]+modes[[j,i,k]]+1-k,{i,Sort[Range[Length[modes[[j]]]],Greater]},{k,Length[modes[[j,i]]]}]//Map[Sort[#,Greater]&,#]&//Catenate},{j,Length[modes]}]//Transpose),{ConstantArray[1,L]}]
]

RiggedToModes[rigged_]:=Module[{L,strings,riggings,r,sMax,MrowLens,firstRow,lastRow,Mmatrix,holes,limits,modes},L=Length[rigged[[1,1]]];
strings=rigged[[2]];
riggings=rigged[[3]];
r=Length[strings];
sMax=Max@Flatten[strings/. {}->0];
MrowLens=Table[Count[strings[[a]],s],{a,r},{s,sMax}];
firstRow=ConstantArray[0,sMax];
firstRow[[1]]=L;
lastRow=ConstantArray[0,sMax];
Mmatrix=PadRight@Join[{firstRow},MrowLens,{lastRow}];
holes=-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[sMax];
limits=((Delete[holes,{{1},{-1}}]+MrowLens)/2)-1/2;
modes=Table[Module[{occ=ConstantArray[0,sMax],rowModes=Table[{},{s,sMax}]},Do[With[{s=strings[[a,n]]},occ[[s]]++;
AppendTo[rowModes[[s]],riggings[[a,n]]-limits[[a,s]]-1+occ[[s]]]],{n,Length[strings[[a]]]}];
Reverse[rowModes]],{a,r}];
modes=Select[modes,AnyTrue[#,(#=!={})&]&];
modes=Map[Reverse,modes];
modes];


(* ::Input::Initialization:: *)
(*Convert a list of strings of form {v[a,s,k]->x,...} where a is the (a+1,0) coordinate, s is the length of the string and k is the number of the string of this type into a list of roots {{x1,x2,...},{...}} where each nested list is a (a,0) coordinate*)
Strings2Roots[strings_]:=Flatten/@Map[Table[#[[2]]-I/2*(#[[1,2]]-1-2k),{k,0,#[[1,2]]-1}]&,GatherBy[strings,#[[1,1]]&],{2}]


(* ::Subsubsection:: *)
(*Equation system for a given mode configuration. To solve.*)


(* ::Input::Initialization:: *)
GenerateSystem[modes_,L_]:=(
BAElog[k_,a_,s_,modeconfig_]:=modeconfig[[a,s,k]]-\[Epsilon]*Sum[Sum[If[{sss,jjj}!={s,k},If[s!=sss,Fsym[2(v[a,s,k]-v[a,sss,jjj])/(s-sss),-1,0],0]+Fsym[2(v[a,s,k]-v[a,sss,jjj])/(s+sss),-1,0]+2Sum[If[nnn!=0,Fsym[(v[a,s,k]-v[a,sss,jjj])/nnn,-1,0],0],{nnn,(s-sss)/2+1,(s+sss)/2-1}],0],{jjj,1,Length[modes[[a,sss]]]}],{sss,1,Length[modes[[1]]]}]+If[a==1,L*Fsym[2*v[a,s,k]/s,-1,0],Sum[Sum[Sum[If[nn!=0,Fsym[(v[a,s,k]-v[a-1,ss,jj])/nn,-1,0],0],{nn,(s-ss)/2+1/2,(s+ss)/2-1/2}],{jj,1,Length[modes[[a-1,ss]]]}],{ss,1,Length[modes[[1]]]}]]+ \[Epsilon]*If[a==Length[modes],0,Sum[Sum[Sum[If[nnnn!=0,Fsym[(v[a,s,k]-v[a+1,ssss,jjjj])/nnnn,-1,0],0],{nnnn,(s-ssss)/2+1/2,(s+ssss)/2-1/2}],{jjjj,1,Length[modes[[a+1,ssss]]]}],{ssss,1,Length[modes[[1]]]}]];
Allrels=Table[BAElog[k,a,s,modes],{a,1,Length[modes]},{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten;
vars=Table[v[a,s,k],{a,1,Length[modes]},{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten;

(*Linear approximations used for predictor*)
J=D[Allrels,{vars}];
fdot=D[Allrels,\[Epsilon]];
)


(* ::Subsubsection:: *)
(*Asymptotic initial conditions*)


(* ::Input::Initialization:: *)
Small\[Epsilon]Expansion[modes_,L_]:=Module[{a},startpredictor={Table[ss/2*Tan[-modes[[1,ss,kk]]Pi/L]//Rationalize[#,10^-prec]&,{ss,Length[modes[[1]]]},{kk,Length[modes[[1,ss]]]}]//Flatten};
While[Length[startpredictor]<Length[modes],a=Length[startpredictor]+1;AppendTo[startpredictor,FindRoot[(Table[(modes[[a,s,k]]//Rationalize[#,10^-prec]&)==-Sum[Sum[Sum[If[nn!=0,Fsym[(v[a,s,k]-v[a-1,ss,jj])/nn,-1,0],0],{nn,(s-ss)/2+1/2,(s+ss)/2-1/2}],{jj,1,Length[modes[[a-1,ss]]]}],{ss,1,Length[modes[[1]]]}],{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten)/.Thread[Rule[Table[v[a-1,ss,jj],{ss,1,Length[modes[[1]]]},{jj,1,Length[modes[[a-1,ss]]]}]//Flatten,startpredictor[[a-1]]]],{Table[v[a,s,k],{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten,
Table[0,{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten}//Transpose,WorkingPrecision->prec,PrecisionGoal->prec,AccuracyGoal->prec/2,MaxIterations->\[Infinity]]//Values]];
startvalue=Thread[vars->(startpredictor//Flatten)]]


(* ::Subsubsection:: *)
(*Corrector*)


(* ::Input::Initialization:: *)
stringfinder[\[Epsilon]0_,predictor_]:=(minsolrep=FindRoot[Allrels/.\[Epsilon]->Rationalize[\[Epsilon]0],{vars,vars/.predictor}//Transpose,WorkingPrecision->prec,PrecisionGoal->prec,AccuracyGoal->prec/2,MaxIterations->\[Infinity]];);


(* ::Subsubsection:: *)
(*Predictor*)


(* ::Input::Initialization:: *)
(*Linear approximation*)
stringpred[solLast_,\[Epsilon]Last_,d\[Epsilon]_]:=Thread[(solLast//Keys)->(solLast//Values)+(LinearSolve[J/.solLast/.\[Epsilon]->\[Epsilon]Last,-fdot/.solLast/.\[Epsilon]->\[Epsilon]Last])*d\[Epsilon]];


(* ::Subsubsection:: *)
(*Step control during iteration*)


(* ::Input::Initialization:: *)
(*Code finding Bethe roots for SU(N), when inputting string length collections and mode numbers; accepting modes from riggedConfig[[i]]*)
IterateString:=Block[{},
step=0.01;
\[Epsilon]Last=\[Epsilon]vals[[-1]];

Monitor[While[\[Epsilon]Last<\[Epsilon]target,
\[Epsilon]new=Min[\[Epsilon]Last+step,\[Epsilon]target];
prednew=stringpred[sol[\[Epsilon]Last],\[Epsilon]Last,step];

stringfinder[\[Epsilon]new,prednew];
sol[\[Epsilon]new]=minsolrep;
AppendTo[\[Epsilon]vals,\[Epsilon]new];
\[Epsilon]Last=\[Epsilon]vals[[-1]]],
Row@{"Current \[Epsilon]: ",\[Epsilon]vals[[-1]]//N," current step: ",step//N}];
];


(* ::Subsubsection:: *)
(*Parameters*)


(* ::Input::Initialization:: *)
prec=40;
\[Epsilon]target=1;

(*(*Step-size control*)
MyMaxIterations=30;*)

(*base=2;pmin=3;RecoverySpeed=1/3;
\[CapitalDelta]q=(base-1)Min[1,RecoverySpeed];*)


(* ::Subsubsection:: *)
(*Calling functions*)


(* ::Input::Initialization:: *)
SolutionFromModeConfiguration[modes_,L_]:=(
\[Epsilon]0=0;
\[Epsilon]vals={\[Epsilon]0};
GenerateSystem[modes,L];
sol[\[Epsilon]0]=Small\[Epsilon]Expansion[modes,L];

IterateString;

{#,Strings2Roots[sol[#]]}&/@\[Epsilon]vals
)
