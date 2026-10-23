(* ::Package:: *)

Get["/Users/thomasscheutz/Documents/UU project on Bethe Ansatz/BEA_project-ZHold/wolfram/Paths.wl"];


Get["/Users/thomasscheutz/Documents/UU project on Bethe Ansatz/BEA_project-ZHold/wolfram/utils/functions.m"]
(*<<"NumericalWBE.m"*)


(* ::Section:: *)
(*SUSY WBE*)


(* ::Subsection::Closed:: *)
(*Qsystem*)


GenerateQsystem[\[Lambda]_] := Block[{},
  Unprotect[M];
  ClearAll[M]; (* Unprotecting because of conflict with Combinatorica package *)

  M[a_, s_, YD_] := M[a, s, YD] = 
    Total[YD] + a s - Total[YD[[1 ;; a]]] - Total[DualDiagram[YD][[1 ;; s]]];

  YQa[0, 0, YD_] := u^Total[YD] + Sum[u^(Total[YD] - k) sym[k], {k, Len}];


  YQa[a_, s_, YD_] := 
    u^M[a, s, YD] + Sum[c[a, s, k] u^(M[a, s, YD] - k), {k, M[a, s, YD]}];

  YQ\[Theta][0, 0, YD_] := YQa[0, 0, YD];

  YQ\[Theta][a_, s_, YD_] := 
    Product[u - q\[Theta][a, s, k], {k, 1, M[a, s, YD]}];
    
  (* QQ relation *)
  QQrel[a_, s_, YD_] := 
    CoefficientList[
      (YQa[a, s, YD] /. u -> u + I/2) (YQa[a + 1, s + 1, YD] /. u -> u - I/2) - 
      (YQa[a, s, YD] /. u -> u - I/2) (YQa[a + 1, s + 1, YD] /. u -> u + I/2) - 
      I (M[a, s, YD] - M[a + 1, s + 1, YD]) YQa[a + 1, s, YD] YQa[a, s + 1, YD], u
    ] /. Complex[0, b_] :> b;

  (* Length of spin chain *)
  Len = Total[\[Lambda]];

  (* Domain of interest is the values of {a, s} for which we are going to check QQ relation
     with Q[a,s] in the top left corner (smallest a, s)
     FullYoungDiagram is maximal possible domain of interest *)
  FullYoungDiagram = Block[{mm}, 
    Flatten@Table[mm[a, s], {a, 0, Length[\[Lambda]] - 1}, {s, 0, \[Lambda][[a + 1]] - 1}] /. mm -> List
  ];

  DomainOfInterest = FullYoungDiagram;

  (* Example of non-standard DomainOfInterest *)
  (* DomainOfInterest = Block[{mm}, Flatten@Table[mm[a, s], {a, 0, 1}, {s, 0, 1}] /. mm -> List]; *)
  
   (* Compute all QQ relations in the domain of interest *)
  Allrel = Monitor[
    Table[
      If[
        MemberQ[DomainOfInterest, {a, s}] && M[a, s, \[Lambda]] > 0,
        QQrel[a, s, \[Lambda]],
        Nothing
      ],
      {a, 0, Length[\[Lambda]] - 1},
      {s, 0, \[Lambda][[a + 1]] - 1}
    ],
    {a, s}
  ] // Flatten;

  (* vars have coefficients of all Q-functions *)
  vars = Table[
    If[a + s == 0, Nothing, c[a, s, k]],
    {a, 0, Length[\[Lambda]] - 1},
    {s, 0, \[Lambda][[a + 1]] - 1},
    {k, M[a, s, \[Lambda]]}
  ] // Flatten;

  (* only those appearing in domain of interest *)
  vars2 = DeleteCases[Variables[Allrel], sym[_]];
];



(* ::Subsection::Closed:: *)
(*SUSYW (THOMAS UPDATED)*)


(*THOMAS UPDATED: added WGrassmann*)
Getmonic[func_]:=func/CoefficientList[func,u][[-1]]
ClearAll[GenerateSusyWronskian]
(*Eq. 2.3*)
nuMarked[yd_, markedPoint_] := Module[
  {
    rowIndex, colIndex, ydT
  },
  {rowIndex, colIndex} = markedPoint;
  ydT = TransposeYoungD[yd];
  
  Table[
    ydT[[i]] - i - rowIndex + colIndex,
    {i, colIndex}
  ]
]
(*Eq. 2.3*)
lambdaMarked[yd_, markedPoint_] := Module[
  {
    rowIndex, colIndex
  },
  {rowIndex, colIndex} = markedPoint;
  
  Table[
    yd[[a]] - a - colIndex + rowIndex,
    {a, rowIndex}
  ]
]

(*eq. 2.19 in Completeness of the Wronskian Bethe ansatz*)(*cP is the chosen Point for which we are currently generating equations, mP is the marked point.*)
  WGrassman[cP_,mP_]:=Block[{noIndices,a,c,\[Mu],\[Nu],sign},
	noIndices=mP-cP;
	a=noIndices//Min;
	c=(noIndices//Max)-a;
	
	Total@(sign Product[Qlocal[c][\[Mu][i],\[Nu][i]],{i,1,a}]Product[Qlocal[c+1-2i][\[Mu][a+i],\[Nu][a+i]],{i,1,c}]
	
	/.If[noIndices[[1]]>=noIndices[[2]],
	{\[Nu][i_]/;i>a:>{},\[Nu][i_]:>{mP[[2]]-i+1},\[Mu][i_]:>{#[[i]]},sign->Signature[#]}&/@Permutations[Range[cP[[1]]+1,mP[[1]]]]
	,
	{\[Mu][i_]/;i>a:>{},\[Mu][i_]:>{mP[[1]]-i+1},\[Nu][i_]:>{#[[i]]},sign->Signature[#]}&/@Permutations[Range[cP[[2]]+1,mP[[2]]]]])


(*THOMAS UDPDATED: new SusyWronskian using WGrassmann; made table allCoeffs*)
GenerateSusyWronskian[mP_, YD_] :=
 Block[{allCoeffs, coeffs,
   SusyWronskian, \[Lambda], \[Nu]},

  \[Lambda] = mP[[1]];
  \[Nu] = mP[[2]];

  \[Lambda]marked := lambdaMarked[YD, mP];
  \[Nu]marked := nuMarked[YD, mP];

  (* Eq. 2.33 *)
  mMarked[A_, J_] := Total[\[Lambda]marked[[#]] & /@ A] +
    Total[\[Nu]marked[[#]] & /@ J] -
    Length[A] (Length[A] - 1)/2 -
    Length[J] (Length[J] - 1)/2 +
    Length[A] Length[J];

  (* Q-polynomial *)
  Q[A_List, J_List] := Module[{m = mMarked[A, J], prefactor},
    prefactor =
      Which[
        Length[A] == 1 && Length[J] == 1,
          -I/(\[Lambda]marked[[First@A]] + \[Nu]marked[[First@J]] + 1),
        True,
          1
      ];

    prefactor u^m +
      Sum[SUSYc[A, J][k] u^(m - k), {k, 1, m}] /.
        SUSYc[A, J][i_] :>
          Which[
            Length[A] == 1 && Length[J] == 0 &&
              MemberQ[\[Lambda]marked, m - i], 0,
            Length[A] == 0 && Length[J] == 1 &&
              MemberQ[\[Nu]marked, m - i], 0,
            True, SUSYc[A, J][i]
          ]/. Complex[0, b_] :> b
  ];
 

  (* === new, robust Solve block here === *)
  (*THOMAS UDPDATED*)
  allCoeffs=Table[
    Module[{m, lhsCoeffs, rhsCoeffs, maxLen, vars, sol},
      m = mMarked[{a}, {i}];

      lhsCoeffs = CoefficientList[
        Expand[(Q[{a}, {i}] /. u -> u + I/2) - (Q[{a}, {i}] /. u -> u - I/2)],
        u
      ];
      rhsCoeffs = CoefficientList[
        Expand[Q[{a}, {}] Q[{}, {i}]],
        u
      ];

      maxLen = Max[Length@lhsCoeffs, Length@rhsCoeffs];
      lhsCoeffs = PadRight[lhsCoeffs, maxLen];
      rhsCoeffs = PadRight[rhsCoeffs, maxLen];

      If[lhsCoeffs[[-1]] =!= 0, lhsCoeffs = lhsCoeffs/lhsCoeffs[[-1]]];

      vars = Table[SUSYc[{a}, {i}][k], {k, 1, m - 1}];

      sol = Solve[Thread[lhsCoeffs == rhsCoeffs], vars];

      If[sol === {} || Head[sol] =!= List,
        Print["No solution for ", {a, i}];
        Abort[]
      ];

      coeffs[{a}, {i}] = First@sol;
    ],
    {a, 1, \[Lambda]}, {i, 1, \[Nu]}
  ]//Flatten;

  (*THOMAS UPDATED*)  
  SusyWronskian=Getmonic@(WGrassman[{0,0},mP]/.Qlocal[n_][A_,J_]:>(Q[A,J]/.u->u+\[HBar]/2 n)/.\[HBar]->I)/.allCoeffs//CoefficientList[#,u]&//Simplify;

  YQ\[Theta][0, 0, YD] := Product[u - \[Theta][i], {i, Total[YD]}];

  <|
    "AllCoeffs" -> allCoeffs,
    "SusyWronskian" -> SusyWronskian,
    "YQ\[Theta]" -> YQ\[Theta][0, 0, YD]
  |>
]



(* ::Subsection::Closed:: *)
(*Path*)


Quiet[Needs["Combinatorica`"]];
(*All paths between points A and B (both coordinates {x,y})*)
PathsAtoB[A_, B_] := Block[{paths,findPaths},
  	paths = {};
  	findPaths[{x_, y_}, {xMax_, yMax_}, currentPath_] := Module[{},
    	If[{x, y} == {xMax, yMax}, AppendTo[paths, currentPath];
     	Return[];];
    	If[x + 1 <= xMax, 
     findPaths[{x + 1, y}, {xMax, yMax}, 
      Append[currentPath, {x + 1, y}]]];
    	If[y + 1 <= yMax, 
     findPaths[{x, y + 1}, {xMax, yMax}, 
      Append[currentPath, {x, y + 1}]]];]
  ; findPaths[A, B, {A}]; 
  paths] 

(*Boundaries of YD*)
Endpoints[\[Lambda]_]:=Join[{{0,\[Lambda][[1]]}},Flatten[Table[{a,s},{a,1,Length[\[Lambda]]-1},{s,\[Lambda][[a+1]],\[Lambda][[a]]}],1],Table[{Length[\[Lambda]],s},{s,0,\[Lambda][[Length[\[Lambda]]]]}]]
 
(*All possible paths from the corner of the Young diagram *)
AllPaths[\[Lambda]_] :=Block[{}, Flatten[PathsAtoB[{0,0}, #] & /@ Endpoints[\[Lambda]], 1]] 

(*Kac-Dynkin path that minimises number of Bethe roots; in case there are several, we store all*)
KDpath[\[Lambda]_] :=Select[AllPaths[\[Lambda]],Total[#, {1, 2}] == Min[Total[AllPaths[\[Lambda]], {2, 3}]] &] 

(*All possible paths from the corner of the Young diagram *)
AllPathssusy[\[Lambda]_] :=Block[{}, Flatten[PathsAtoB[{0,0}, #] & /@ Endpoints[\[Lambda]], 1]] 


(* ::Section:: *)
(*Functions*)


(* ::Subsection::Closed:: *)
(*Compute C-coefficient to SUSY-coefficient (new) (THOMAS UPDATED)*)


(*THOMAS UPDATED: removed iterative solution method*)
Computec2susyCoefficientsv2[yd_, mP_] := Module[
  {indices, allTaggedEqns, allEqnsOnly, allCVars, knownVars, 
   remainingCVars, selectedPairs, candidates, bestPair, foundVar, 
   finalEqns, cSolution},
  
  (* 1. Generate indices based on mP (excluding {0,0}) *)
  
  indices = (Tuples[Range[0, #] & /@ mP] // Reverse) /. {{0, 0} -> Nothing};

  (* 2. Generate Equations *)
  allTaggedEqns = Flatten[
	Table[  
	  CoefficientList[
	        YQa[idx[[1]], idx[[2]], yd]
	        -
	        Getmonic@(
	        WGrassman[{idx[[1]],idx[[2]]},mP]
	        /.Qlocal[n_][A_,J_]:>(Q[A,J]/.u->u+\[HBar]/2 n)/.\[HBar]->I), 
	        u
	      ]
	  ,{idx,indices}]];
      
  (* 3. Solve equations *)
  allEqnsOnly = allTaggedEqns[[All, 2]];
  
  allCVars = Union[Cases[Variables[allEqnsOnly], c[__]]];
  
  cSolution = Solve[allEqnsOnly == 0, allCVars]//Quiet//First
  ];


(* ::Subsection::Closed:: *)
(*Compute SUSY-coefficient to C-coefficient ( Only up to mP) (THOMAS UPDATED)*)


(*THOMAS UPDATED: new iterative algorithm*)
(* Function Definition *)
Computesusy2cCoefficientsv3[YD_, mP_] := Module[
  {eqsBetF,knownSUSYc},
  
(*Find SUSYc[{},{i}][n] and SUSYc[{a},{}][n]*)
(*find equations on the variables by moving in the bosonic or fermionic direction*)
eqsBetF=Join[

Table[CoefficientList[YQa[mP[[1]],i,YD]-Getmonic@(WGrassman[{mP[[1]],
		i},mP]/.Qlocal[n_][A_,J_]:>(Q[A,J]/.u->u+\[HBar]/2 n)/.\[HBar]->I),u][[Total[\[Nu]marked[[i+2;;]]]
		+Complement[Range[0,Max@\[Nu]marked[[i+1;;]]],\[Nu]marked[[i+1;;]]][[;;]]-
		(mP[[2]]-i)((mP[[2]]-i)-1)/2+1]],{i,0,mP[[2]]-1}
	]
,
Table[CoefficientList[YQa[i,mP[[2]],YD]-
		Getmonic@(WGrassman[{i,mP[[2]]},mP]/.Qlocal[n_][A_,J_]:>(Q[A,
		J]/.u->u+\[HBar]/2 n)/.\[HBar]->I),u][[Total[\[Lambda]marked[[i+2;;]]]
		+Complement[Range[0,Max@\[Lambda]marked[[i+1;;]]],\[Lambda]marked[[i+1;;]]]-
		(mP[[1]]-i)((mP[[1]]-i)-1)/2+1]],{i,0,mP[[1]]-1}
	]
]//Flatten;

(*find the variables by solving the equations*)
knownSUSYc=First@Solve[eqsBetF==0,Variables[eqsBetF]/.c[___]->Nothing/.sym[___]->Nothing];

(*Find SUSY[{a},{i}][n]*)
(*generate equations by going in a snake from the marked point to the origin*)
Do[eqsBFAt[j,i]=SelectFirst[CoefficientList[YQa[j,i,YD]
		-Getmonic@(WGrassman[{j,i},mP]/.Qlocal[n_][A_,J_]:>(Q[A,J]/.u->u+\[HBar]/2 n)/.\[HBar]->I),u],
		MemberQ[Variables[#],SUSYc[{j+1},{i+1}][mMarked[{j+1},{i+1}]]]&]
	,{i,0,mP[[2]]-1},{j,0,mP[[1]]-1}];

(*solve the equations iteratively*)
Do[AppendTo[knownSUSYc,First@Solve[(eqsBFAt[j,i]/.allCoeffs/.knownSUSYc)==0,{SUSYc[{j+1},{i+1}][mMarked[{j+1},{i+1}]]}]];
knownSUSYc=Flatten@knownSUSYc
,{i,mP[[2]]-1,0,-1},{j,mP[[1]]-1,0,-1}];
knownSUSYc
];
