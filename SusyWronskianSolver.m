(* ::Package:: *)

SetDirectory[NotebookDirectory[]]
<<"functions.m"
<<"NumericalWBE.m"
<<"StringSolverRK.m"


(* ::Section:: *)
(*SUSY WBE*)


(* ::Subsection::Closed:: *)
(*SUSYW*)


Getmonic[func_]:=func/CoefficientList[func,u][[-1]]


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
   Q[A_List, J_List] := Module[{m = mMarked[A, J], prefactor},

  prefactor =
    Which[
      Length[A] == 1 && Length[J] == 1,
        - I/(\[Lambda]marked[[A//First]] + \[Nu]marked[[J//First]] + 1),

      True,
        1
    ];
    prefactor =
    Which[
      Length[A] >= 1 && Length[J] >= 1,
        - I/(mMarked[A, J]),

      True,
        1
    ];

  prefactor u^m +
    Sum[c[A, J][k] u^(m - k), {k, 1, m}] /. 
      c[A, J][i_] :>
        Which[
          Length[A] == 1 && Length[J] == 0 &&
            MemberQ[\[Lambda]marked, m - i], 0,

          Length[A] == 0 && Length[J] == 1 &&
            MemberQ[\[Nu]marked, m - i], 0,

          True, c[A, J][i]
        ]
]
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



(* ::Subsection::Closed:: *)
(*Path*)


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


(* ::Subsection::Closed:: *)
(*Marked Points*)


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


(* ::Section::Closed:: *)
(*For Debugg*)


(* ::Input:: *)
(*Q[A_List, J_List] := Module[{m = mMarked[A, J], prefactor},*)
(**)
(*  prefactor =*)
(*    Which[*)
(*      Length[A] == 1 && Length[J] == 1,*)
(*        -I/(\[Lambda]marked[[A//First]] + \[Nu]marked[[J//First]] + 1),*)
(**)
(*      True,*)
(*        1*)
(*    ];*)
(**)
(*  prefactor u^m +*)
(*    Sum[c[A, J][k] u^(m - k), {k, 1, m}] /. *)
(*      c[A, J][i_] :>*)
(*        Which[*)
(*          Length[A] == 1 && Length[J] == 0 &&*)
(*            MemberQ[\[Lambda]marked, m - i], 0,*)
(**)
(*          Length[A] == 0 && Length[J] == 1 &&*)
(*            MemberQ[\[Nu]marked, m - i], 0,*)
(**)
(*          True, c[A, J][i]*)
(*        ]*)
(*]*)
(**)


(* ::Input:: *)
(*(*Solve Eq. 2.21 in Chernyak&Volin*)*)
(*Do[*)
(*  Module[{lhsCoeffs, rhsCoeffs, cfs},*)
(*    *)
(*    (* Compute coefficient list of shifted difference *)*)
(*    cfs = CoefficientList[*)
(*      (Q[{a}, {i}] /. u -> u + I/2) - (Q[{a}, {i}] /. u -> u - I/2),*)
(*      u*)
(*    ];*)
(*    *)
(*    (* LHS coefficients *)*)
(*    lhsCoeffs = cfs / cfs[[-1]];*)
(*    *)
(*    (* RHS coefficients *)*)
(*    rhsCoeffs = CoefficientList[Q[{a}, {}] Q[{}, {i}], u];*)
(*    *)
(*    (* Solve for the inner coefficients of Q[{a}, {i}] *)*)
(*    coeffs[{a}, {i}] = *)
(*      First @ Solve[*)
(*        lhsCoeffs - rhsCoeffs == 0,*)
(*        CoefficientList[Q[{a}, {i}], u][[2 ;; -2]]*)
(*      ];*)
(*  ],*)
(*  {a, 1, mP[[1]]},*)
(*  {i, 1, mP[[2]]}*)
(*]*)
(**)
(**)


(* ::Input:: *)
(*fermlist := Table[*)
(*  Module[{Qi},*)
(*    Qi = Q[{i}, {j}] /. coeffs[{i}, {j}];*)
(*    Qi /. u -> u + \[HBar] * ((mP[[1]] - mP[[2]])/2) /. \[HBar] -> I*)
(*    *)
(*  ],*)
(*  {i, mP[[1]]},*)
(*  {j, mP[[2]]}*)
(*]*)
(**)
(*boslist := Table[*)
(*  Module[{Qi, shift},*)
(*    *)
(*    Qi = Q[{i}, {}];*)
(*    shift = \[HBar] * ((mP[[1]] - mP[[2]] - 2 j + 1)/2);*)
(*    Qi /. u -> u + shift /. \[HBar] -> I*)
(*    *)
(*  ],*)
(*  {i, mP[[1]]},*)
(*  {j, mP[[1]] - mP[[2]]}*)
(*]*)
(**)
(*(*The equation 2.20 in Chernyak & Volin*)*)
(*SusyWronskian=(-1)^(mP[[2]](mP[[1]]-mP[[2]]))Det[ArrayFlatten[{{fermlist,boslist}}]]; (*The RHS of 2.20 in Chernyak&Volin*)*)
(*YQ\[Theta][0,0,YD_]:=Product[u-\[Theta][i],{i,Total[YD]}] (*The LHS of 2.20*)*)
(**)
(*CoefficientList[SusyWronskian,u]//Length*)
(*CoefficientList[YQ\[Theta][0,0,yd],u]//Length*)
(**)
(*vars = Rest[Variables[SusyWronskian]];*)
(*eqs = CoefficientList[*)
(*   SusyWronskian/(CoefficientList[SusyWronskian, u][[-1]]) - LocalYQ\[Theta],*)
(*   u*)
(*]/.(Variables[CoefficientList[LocalYQ\[Theta],u]]/.\[Theta][i__]:>\[Theta][i]->0);*)
(*mysol = NSolve[eqs==0,vars]*)


(* ::Input:: *)
(*fermlist=Table[(Q[{i},{j}]/.coeffs[{i},{j}])/. u -> (u + hbar*((mP[[1]]-mP[[2]])/2 )),{i,mP[[1]]},{j,mP[[2]]}];*)
(*boslist=Table[(Q[{i},{}])/. u -> (u + hbar*((mP[[1]]-mP[[2]]-2j+1)/2 )),{i,mP[[1]]},{j,mP[[1]]-mP[[2]]}]/.hbar->I;*)


(* ::Section:: *)
(*Run SUSY WBE*)


(* ::Input:: *)
(*(*Example Bosonic BAE for yd = {4,2,1}*)*)
(*yd = {4,2,1};*)
(*mP={3,1};*)
(*\[Lambda]marked=lambdaMarked[yd,mP]*)
(*\[Nu]marked=nuMarked[yd,mP]*)
(**)
(*susyresult= GenerateSusyWronskian[mP,yd];*)
(*SusyWronskian =susyresult[["SusyWronskian"]];*)
(*LocalYQ\[Theta] = susyresult[["YQ\[Theta]"]];*)
(*vars = Rest[Variables[SusyWronskian]];*)
(*eqs = CoefficientList[*)
(*   SusyWronskian/(CoefficientList[SusyWronskian, u][[-1]]) - LocalYQ\[Theta],*)
(*   u*)
(*]/.(Variables[CoefficientList[LocalYQ\[Theta],u]]/.\[Theta][i__]:>\[Theta][i]->0);*)
(**)
(*mysol = NSolve[eqs==0,vars];*)
(*Length@mysol*)


(* ::Input:: *)
(*(*Eq. 5.7*)*)
(*Qbblocal[a_, s_] := Qlocal[Range[a + 1, mP[[1]]], Range[s + 1, mP[[2]]]]*)
(*(*EvalQFunction find the distinguished Q function in Subscript[Q, A|B] and reduce A and B recursive into single indices using QQ-relations*)*)
(*EvalQFunction[a_,s_]:=ExpandQ[Qbblocal[a,s]]*)
(**)
(*r20=Table[Solve[(EvalQFunction[2,0]/.mysol[[j]])==0,u],{j,Length@mysol}]//Values//Flatten;*)
(*r10=Table[Solve[(EvalQFunction[1,0]/.mysol[[j]])==0,u],{j,Length@mysol}]//Values//Flatten;*)
(*ComplexListPlot[{r20,r10},PlotRange->All]*)


wQQb[a_, i_] := 
 Module[{eq1, eq2,eqc1,eqc2, sol},
  
  (* original two sides *)
  eq1 = Q[{a},{}] * Q[{},{i}];
  
  eq2 = ((Q[{a},{i}]/.u->u+I/2)-(Q[{a},{i}]/.u->u-I/2))//Getmonic;
  
  (* coefficient lists in u *)
  eqc1 = CoefficientList[eq1, u];
  eqc2 = CoefficientList[eq2, u];

  (* solve for the c[A,J][k] variables *)
  sol = Solve[eqc1 - eqc2 == 0, Variables[eqc2]] // First;
  
  sol
]


(*Function reduce multi index of Q function into single index using QQ-relations*)
ClearAll[ExpandQ];
ExpandQ[expr_] := expr /. Qlocal[a_List, j_List] :> expandQsingle[Qlocal[a, j]];

ExpandQ[expr_] := 
 Module[{tmp},
   tmp = expr /. Qlocal[a_List, j_List] :> expandQsingle[Qlocal[a, j]]
   (*tmp /. {Qlocal -> Q,Wronlocal->Wron}*)
 ];
 
ClearAll[ExpandQ];

ExpandQ[expr_] := Module[{},

  (* 2. Apply recursive expansion *)
  tmp = expr /. Qlocal[a_List, j_List] :> expandQsingle[Qlocal[a, j]];
  (* 1. Extract all mixed Q\[CloseCurlyQuote]s: Qlocal[{a},{i}]  *)
  mixedQs = DeleteDuplicates @ Cases[
     tmp,
     Qlocal[a_List, j_List] /; Length[a] == 1 && Length[j] == 1 :> {a//First,j//First},
     Infinity
  ];
  
  localwQQb = (wQQb @@ # & /@ mixedQs)//Flatten;

  tmp /. {Qlocal -> Q,Wronlocal->Wron}/.localwQQb
];
 
ClearAll[expandQsingle];
expandQsingle[Qlocal[A_List, J_List]] := expandQsingle[Qlocal[A, J]] =
  Module[{lenA, lenJ, A0, a, b, J0, i, j},
    lenA = Length[A];
    lenJ = Length[J];
    Which[
      (* base case: already single-index (or empty) on both sides *)
      lenA <= 1 && lenJ <= 1,
        Qlocal[A, J],

      (* reduce bosonic indices using: 
         Q_{Aab|I} Q_{A|I} = W(Q_{Aa|I}, Q_{Ab|I}) *)
      lenA >= 2,
        A0 = Take[A, lenA - 2];
        a  = A[[-2]];
        b  = A[[-1]];
        Wronlocal[
         { expandQsingle[Qlocal[Join[A0, {a}], J]],
          expandQsingle[Qlocal[Join[A0, {b}], J]]}
        ] / expandQsingle[Qlocal[A0, J]],

      (* reduce fermionic indices using:
         Q_{A|Iij} Q_{A|I} = W(Q_{A|Ii}, Q_{A|Ij}) *)
      lenJ >= 2,
        J0 = Take[J, lenJ - 2];
        i  = J[[-2]];
        j  = J[[-1]];
        Wronlocal[
          {expandQsingle[Qlocal[A, Join[J0, {i}]]],
          expandQsingle[Qlocal[A, Join[J0, {j}]]]}
        ] / expandQsingle[Qlocal[A, J0]]
    ]
  ];



ClearAll[wQQa]
wQQa[A_List, II_List, a_, b_] := 
 Module[{eq1, eq2, eqc1, eqc2, sol},
  
  eq1 = Q[Join[A, {a}, {b}], II];
  eq2 = Wron[{Q[Join[A, {a}], II], Q[Join[A, {b}], II]}]/Q[A, II];
  
  eqc1 = CoefficientList[eq1, u];
  eqc2 = CoefficientList[eq2, u]/CoefficientList[eq2, u][[-1]];
  
  sol = Solve[eqc1 - eqc2 == 0, Variables[eqc1]] // First;
  sol
]


(*Eq. 5.8*)
QQbbrel[a_, s_]:=Wron[{Qbb[a+1,s+1] ,Qbb[a,s]}]-Qbb[a+1,s]Qbb[a,s+1]


(*Eq. 2.19*)
ClearAll[Qasy]
Qasy[w_, b_] := 
  1/(w! b!) *
   Sum[
     Subscript[
       Q,
       Row[Flatten[{
         Table[Subscript[a, i], {i, 1, w}],
         "|",
         Table[Subscript[i, q], {q, 1, b}]
       }]]
     ] *
     Dot @@ Table[Subscript[\[Psi], 0]^Subscript[a, i], {i, 1, w}] *
     Dot @@ Table[Subscript[\[Psi], 1]^Subscript[i, q], {q, 1, b}],
     Evaluate[Sequence @@ Table[{Subscript[a, i], 1, w}, {i, w}]],
     Evaluate[Sequence @@ Table[{Subscript[i, q], 1, b}, {q, b}]]
   ];
(* Fermionic \[Psi]0, \[Psi]1: anticommute within each family and square to 0 *)
ClearAll[\[Psi]0, \[Psi]1];
Unprotect[Dot];

(* Nilpotency: any repeated index makes the dotted product zero *)
\[Psi]0 /: Dot[pre___, \[Psi]0[a_], mid___, \[Psi]0[a_], post___] := 0;
\[Psi]1 /: Dot[pre___, \[Psi]1[i_], mid___, \[Psi]1[i_], post___] := 0;

(* Anticommutation within each family: reorder to a canonical order with a sign *)
\[Psi]0 /: Dot[pre___, \[Psi]0[a_], \[Psi]0[b_], post___] /; OrderedQ[{b, a}] := -Dot[pre, \[Psi]0[b], \[Psi]0[a], post];
\[Psi]1 /: Dot[pre___, \[Psi]1[i_], \[Psi]1[j_], post___] /; OrderedQ[{j, i}] := -Dot[pre, \[Psi]1[j], \[Psi]1[i], post];

Protect[Dot];

Clear[QasyFermi]
QasyFermi[w_, b_, aRange_: Automatic, iRange_: Automatic] := Module[
  {aIdx, iIdx, aIter, iIter, aCond, iCond},
  aIdx = Table[Subscript[a, i], {i, 1, w}];
  iIdx = Table[Subscript[i, q], {q, 1, b}];
  aIter = If[aRange === Automatic, Table[{aIdx[[k]], 1, Infinity}, {k, w}], 
             MapThread[List, {aIdx, aRange}]];
  iIter = If[iRange === Automatic, Table[{iIdx[[k]], 1, Infinity}, {k, b}], 
             MapThread[List, {iIdx, iRange}]];
  aCond = And @@ Thread[Differences[aIdx] > 0];
  iCond = And @@ Thread[Differences[iIdx] > 0];
  Sum[
    Boole[aCond && iCond] *
    Subscript[Q, Row[Flatten[{aIdx, "|", iIdx}]]] *
    (Dot @@ Table[Subscript[\[Psi], 0]^aIdx[[k]], {k, w}]) *
    (Dot @@ Table[Subscript[\[Psi], 1]^iIdx[[q]], {q, b}]),
    Evaluate[Sequence @@ aIter],
    Evaluate[Sequence @@ iIter]
  ]
];

Qasy[1,1]
Qasy[2,1]


(* ::Input:: *)
(*1/2 ( Subscript[Q, Row[{1,2,"|",1}]]- Subscript[Q, Row[{2,1,"|",1}]] )*)


(* ::Input:: *)
(*(*QQ-relations Eq 2.17 *)*)
(*WQQa[A_List, I_List, a_, b_] :=*)
(*  Q[Join[A, {a}, {b}], I]  == *)
(*  Wron[{Q[Join[A, {a}], I], Q[Join[A, {b}], I]}]/Q[A, I]*)
(*WQQb[A_List, I_List, a_, i_] :=*)
(*  Q[Join[A, {a}], I] Q[A, Join[I,{i}]] - *)
(*  Wron[{Q[Join[A, {a}], Join[I, {i}]], Q[A, I]}]/Wron[{Q[Join[A, {a}], Join[I, {i}]], Q[A, I]}]*)
(*WQQc[A_List, I_List, i_, j_] :=*)
(*  Q[A,Join[I, {i}, {j}]] Q[A, I] - *)
(*  Wron[{Q[ A, Join[I, {i}]], Q[A,Join[I, {j}]]}]*)
(**)
(*(*Eq. 5.7*)*)
(*Qbb[a_, s_] := Q[Range[a + 1, mP[[1]]], Range[s + 1, mP[[2]]]]*)
(**)
(*lessEqualmPDomain = (Table[{a, s}, {a, 0, mP[[1]]}, {s, 0, mP[[2]]}] // Flatten[#, 1] &)//Rest*)
(*Table[*)
(*  With[{a = pair[[1]], b = pair[[2]]},*)
(*    Qbb[a, b]*)
(*  ],*)
(*  {pair, lessEqualmPDomain}*)
(*]//MatrixForm;*)


(* ::Input:: *)
(*a=0;s=1*)
(*a=1;s=0*)
(*Wron[{Qbb[a+1,s+1] ,Qbb[a,s]}]-(-I(Qbb[a+1,s]Qbb[a,s+1]))*)
(*expr=CoefficientList[Wron[{EvalQFunction[a+1,s+1] ,EvalQFunction[a,s]}]-(-I(EvalQFunction[a+1,s]EvalQFunction[a,s+1])),u]*)
(*vars = Variables[expr]*)
(*Solve[expr==0,vars]*)
