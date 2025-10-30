(* ::Package:: *)

Quiet[Needs["Combinatorica`"]];
(*All paths between points A and B (both coordinates {x,y})*)
PathsAtoB[A_, B_] := Block[{paths},
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


(*Eq. 2.3*)
nuMarked[yd_, markedPoint_] := Module[
  {
    rowIndex, colIndex, ydT
  },
  {rowIndex, colIndex} = markedPoint;
  ydT = TransposePartition[yd];
  
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

(*Eq. 2.33*)
mMarked[A_, J_] := Module[
  {
    sumLambda, sumNu, lenA, lenJ
  },
  
  sumLambda = Total[\[Lambda]marked[[#]] & /@ A];
  sumNu     = Total[\[Nu]marked[[#]] & /@ J];
  lenA      = Length[A];
  lenJ      = Length[J];
  
  sumLambda + sumNu
    - lenA (lenA - 1)/2
    - lenJ (lenJ - 1)/2
    + lenA lenJ
]


Q[A_List, J_List] :=
  u^mMarked[A, J] +
    Sum[c[A, J][k] u^(mMarked[A, J] - k), {k, 1, mMarked[A, J]}] /. 
   c[A, J][i_] :>
     Which[
       Length[A] == 1 && Length[J] == 0 && MemberQ[\[Lambda]marked, mMarked[A, J] - i], 0,
       Length[A] == 0 && Length[J] == 1 && MemberQ[\[Nu]marked, mMarked[A, J] - i], 0,
       True, c[A, J][i]
     ]


(*Solve Eq. 2.21 in Chernyak&Volin*)
Do[
  Module[{lhsCoeffs, rhsCoeffs, cfs},
    
    (* Compute coefficient list of shifted difference *)
    cfs = CoefficientList[
      (Q[{a}, {i}] /. u -> u + I/2) - (Q[{a}, {i}] /. u -> u - I/2),
      u
    ];
    
    (* LHS coefficients *)
    lhsCoeffs = cfs / cfs[[-1]];
    
    (* RHS coefficients *)
    rhsCoeffs = CoefficientList[Q[{a}, {}] Q[{}, {i}], u];
    
    (* Solve for the inner coefficients of Q[{a}, {i}] *)
    coeffs[{a}, {i}] = 
      First @ Solve[
        lhsCoeffs - rhsCoeffs == 0,
        CoefficientList[Q[{a}, {i}], u][[2 ;; -2]]
      ];
  ],
  {a, 1, mP[[1]]},
  {i, 1, mP[[2]]}
]




fermlist := Table[
  Module[{Qi},
    Qi = Q[{i}, {j}] /. coeffs[{i}, {j}];
    Qi /. u -> u + \[HBar] * ((mP[[1]] - mP[[2]])/2) /. \[HBar] -> I
    
  ],
  {i, mP[[1]]},
  {j, mP[[2]]}
]

boslist := Table[
  Module[{Qi, shift},
    
    Qi = Q[{i}, {}];
    shift = \[HBar] * ((mP[[1]] - mP[[2]] - 2 j + 1)/2);
    Qi /. u -> u + shift /. \[HBar] -> I
    
  ],
  {i, mP[[1]]},
  {j, mP[[1]] - mP[[2]]}
]

(*The equation 2.20 in Chernyak & Volin*)
SusyWronskian=(-1)^(mP[[2]](mP[[1]]-mP[[2]]))Det[ArrayFlatten[{{fermlist,boslist}}]] (*The RHS of 2.20 in Chernyak&Volin*)
YQ\[Theta][0,0,YD_]:=Product[u-\[Theta][i],{i,Total[YD]}] (*The LHS of 2.20*)


(* ::Input:: *)
(*fermlist=Table[(Q[{i},{j}]/.coeffs[{i},{j}])/. u -> (u + hbar*((mP[[1]]-mP[[2]])/2 )),{i,mP[[1]]},{j,mP[[2]]}];*)
(*boslist=Table[(Q[{i},{}])/. u -> (u + hbar*((mP[[1]]-mP[[2]]-2j+1)/2 )),{i,mP[[1]]},{j,mP[[1]]-mP[[2]]}]/.hbar->I;*)


ClearAll[GenerateSusyWronskian]
GenerateSusyWronskian[mP_, YD_] :=
 Block[{\[Nu]marked, \[Lambda]marked, coeffs, fermlist, boslist, SusyWronskian, \[Lambda], \[Nu]},

  \[Lambda] = mP[[1]];
  \[Nu] = mP[[2]];

  \[Lambda]marked = lambdaMarked[YD, mP];
  \[Nu]marked = nuMarked[YD, mP];

  (* Eq. 2.33 *)
  mMarked[A_, J_] := Total[\[Lambda]marked[[#]] & /@ A] + 
    Total[\[Nu]marked[[#]] & /@ J] -
    Length[A] (Length[A] - 1)/2 -
    Length[J] (Length[J] - 1)/2 +
    Length[A] Length[J];

  (* Q-polynomial definition with numeric \[Lambda],\[Nu] fixed *)
  With[{\[Lambda] = \[Lambda], \[Nu] = \[Nu]},
   Q[A_List, J_List] :=
    u^mMarked[A, J] +
     Sum[c[A, J][k] u^(mMarked[A, J] - k), {k, 1, mMarked[A, J]}] /. 
      c[A, J][i_] :>
       Which[
        Length[A] == 1 && Length[J] == 0 && MemberQ[\[Lambda]marked, mMarked[A, J] - i], 0,
        Length[A] == 0 && Length[J] == 1 && MemberQ[\[Nu]marked, mMarked[A, J] - i], 0,
        True, c[A, J][i]
       ];
   ];

  (* === Solve Eq. 2.21 === *)
  Do[
   Module[{lhsCoeffs, rhsCoeffs, cfs},
    cfs = CoefficientList[
      (Q[{a}, {i}] /. u -> u + I/2) - (Q[{a}, {i}] /. u -> u - I/2),
      u
    ];
    lhsCoeffs = cfs / cfs[[-1]];
    rhsCoeffs = CoefficientList[Q[{a}, {}] Q[{}, {i}], u];
    coeffs[{a}, {i}] =
      First@Solve[
        lhsCoeffs - rhsCoeffs == 0,
        CoefficientList[Q[{a}, {i}], u][[2 ;; -2]]
      ];
    ],
   {a, 1, \[Lambda]}, {i, 1, \[Nu]}
  ];

  (* === Build fermionic list === *)
  fermlist = Table[
    Module[{Qi},
      Qi = Q[{i}, {j}] /. coeffs[{i}, {j}];
      Qi /. u -> u + I*((\[Lambda] - \[Nu])/2)
    ],
    {i, \[Lambda]}, {j, \[Nu]}
  ];

  (* === Build bosonic list === *)
  boslist = Table[
    Module[{Qi, shift},
      Qi = Q[{i}, {}];
      shift = I*((\[Lambda] - \[Nu] - 2 j + 1)/2);
      Qi /. u -> u + shift
    ],
    {i, \[Lambda]}, {j, \[Lambda] - \[Nu]}
  ];

  (* === Supersymmetric Wronskian Eq. 2.20 === *)
  SusyWronskian = (-1)^(\[Nu] (\[Lambda] - \[Nu])) * Det[ArrayFlatten[{{fermlist, boslist}}]];

  (* === Define LHS polynomial === *)
  YQ\[Theta][0, 0, YD] := Product[u - \[Theta][i], {i, Total[YD]}];

  <|
    "FermList" -> fermlist,
    "BosList" -> boslist,
    "SusyWronskian" -> SusyWronskian,
    "YQ\[Theta]" -> YQ\[Theta][0, 0, YD]
  |>
]



(* Page 20. Example of gl_{1|1}*)
yd ={2,1};
mP={2,0};
\[Lambda]marked=lambdaMarked[yd,mP]
\[Nu]marked=nuMarked[yd,mP]

SusyWronskian = GenerateSusyWronskian[mP,yd][["SusyWronskian"]];
LocalYQ\[Theta] = GenerateSusyWronskian[mP,yd][["YQ\[Theta]"]];
vars = Rest[Variables[SusyWronskian]];
eqs=CoefficientList[SusyWronskian,u]/CoefficientList[SusyWronskian,u][[-1]]-CoefficientList[LocalYQ\[Theta],u]/.(Rest[Variables[LocalYQ\[Theta]]]/.\[Theta][i__]:>\[Theta][i]->0);
mysol = NSolve[eqs==0,vars]


(*QQ-relations Eq.17 *)
WQQa[A_List, I_List, a_, b_] :=
  Q[Join[A, {a}, {b}], I]  == 
  Wron[{Q[Join[A, {a}], I], Q[Join[A, {b}], I]}]/Q[A, I]
WQQb[A_List, I_List, a_, i_] :=
  Q[Join[A, {a}], I] Q[A, Join[I,{i}]] - 
  Wron[{Q[Join[A, {a}], Join[I, {i}]], Q[A, I]}]/Wron[{Q[Join[A, {a}], Join[I, {i}]], Q[A, I]}]
WQQc[A_List, I_List, i_, j_] :=
  Q[A,Join[I, {i}, {j}]] Q[A, I] - 
  Wron[{Q[ A, Join[I, {i}]], Q[A,Join[I, {j}]]}]

(*Eq. 5.7*)
Qbb[a_, s_] := Q[Range[a + 1, mP[[1]] ], Range[s + 1, mP[[2]]]]

lessEqualmPDomain = (Table[{a, s}, {a, 0, mP[[1]]}, {s, 0, mP[[2]]}] // Flatten[#, 1] &)//Rest
Table[
  With[{a = pair[[1]], b = pair[[2]]},
    Qbb[a, b]
  ],
  {pair, lessEqualmPDomain}
]//MatrixForm


Variables[CoefficientList[LocalYQ\[Theta],u]]


(*Example Bosonic BAE for yd = {4,2,1}*)
yd = {4,2,1};
mP={3,0};
\[Lambda]marked=lambdaMarked[yd,mP]
\[Nu]marked=nuMarked[yd,mP]
GenerateSusyWronskian[mP,yd];
 
SusyWronskian = GenerateSusyWronskian[mP,yd][["SusyWronskian"]];
LocalYQ\[Theta] = GenerateSusyWronskian[mP,yd][["YQ\[Theta]"]];
vars = Rest[Variables[SusyWronskian]];
eqs=CoefficientList[SusyWronskian,u]/CoefficientList[SusyWronskian,u][[-1]]-CoefficientList[LocalYQ\[Theta],u]/.(Variables[CoefficientList[LocalYQ\[Theta],u]]/.\[Theta][i__]:>\[Theta][i]->0);
mysol = NSolve[eqs==0,vars];


(*Bethe roots*)
r20=Table[Solve[(Qbb[2,0]/.mysol[[j]])==0,u],{j,Length@mysol}]//Values//Flatten;
r10=Table[Solve[((I u)/2+2 I u^3+1/4 I c[{2},{}][1]+I u^2 c[{2},{}][1]-I c[{2},{}][3]-1/4 I c[{3},{}][1]+3 I u^2 c[{3},{}][1]+2 I u c[{2},{}][1] c[{3},{}][1]/.mysol[[j]])==0,u],{j,Length@mysol}]//Values//Flatten//Sort;


r10//ComplexListPlot
