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
    Qi /. u -> u + \[HBar] * ((mP[[1]] - mP[[2]])/2)
    
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


(* Page 20. Example of gl_{1|1}*)
(*Does not works for {0,2},{2,0}*)
yd = {2,1};
KDpath[yd][[All,-1]]

markedPoint[yd_]:=KDpath[yd][[2,-1]]
mP=markedPoint[yd]
\[Lambda]marked=lambdaMarked[yd,mP]
\[Nu]marked=nuMarked[yd,mP]
mMarked[{1},{1}];

Q[{1},{}]
Q[{},{1}]
Q[{},{}]

vars = Rest[Variables[SusyWronskian]]
Solve[CoefficientList[SusyWronskian-YQ\[Theta][0,0,yd],u]==0/.{\[Theta][1]->0, \[Theta][2]->0,\[Theta][3]->0},vars]//N



