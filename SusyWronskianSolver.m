(* ::Package:: *)

SetDirectory[NotebookDirectory[]]
<<"functions.m"
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
(*SUSYW*)


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


GenerateSusyWronskian[mP_, YD_] :=
 Block[{ coeffs, fermlist, boslist,
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
  Do[
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
  ];

  (* Fermionic list *)
  fermlist = Table[
    Module[{Qi},
      Qi = Q[{i}, {j}] /. coeffs[{i}, {j}];
      Qi /. u -> u + I*((\[Lambda] - \[Nu])/2)
    ],
    {i, \[Lambda]}, {j, \[Nu]}
  ];

  (* Bosonic list *)
  boslist = Table[
    Module[{Qi, shift},
      Qi = Q[{i}, {}];
      shift = I*((\[Lambda] - \[Nu] - 2 j + 1)/2);
      Qi /. u -> u + shift
    ],
    {i, \[Lambda]}, {j, \[Lambda] - \[Nu]}
  ];

  SusyWronskian =
    (-1)^(\[Nu] (\[Lambda] - \[Nu])) *
      Det[ArrayFlatten[{{fermlist, boslist}}]];

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


(* ::Subsection:: *)
(*Generate Equations*)


(*Eq. 5.7*)
Qbblocal[a_, s_] := Qlocal[Range[a + 1, mP[[1]]], Range[s + 1, mP[[2]]]]
(*EvalQFunction find the distinguished Q function in Subscript[Q, A|B] and reduce A and B recursive into single indices using QQ-relations*)
EvalQFunction[a_,s_]:=ExpandQ[Qbblocal[a,s]]

eqnsFor[{a_, s_},yd_,mP_] := Module[{rhs},
  GenerateSusyWronskian[mP,yd][["SusyWronskian"]];
  GenerateQsystem[yd];
  (* special case: (a,s) = (0,0) *)
  rhs = If[a == 0 && s == 0,
    Getmonic @ GenerateSusyWronskian[mP,yd][["SusyWronskian"]],
    Getmonic @ EvalQFunction[a, s]
  ];
  
  CoefficientList[
    YQa[a, s, yd] - rhs,
    u
  ]
]

varsFor[{a_, s_},yd_,mP_] :=
  If[a == 0 && s == 0,
    (* variables come from SusyWronskian instead of EvalQFunction *)
    GenerateSusyWronskian[mP,yd];
    Variables[GenerateSusyWronskian[mP,yd][["SusyWronskian"]]] /. u -> Nothing,
    Variables[EvalQFunction[a, s]] /. u -> Nothing
  ];




(* ::Subsection:: *)
(*Compute C-coefficient to SUSY-coefficient (old)*)


(*Straightforwar; however, for the (2,1), 
    some C-coefficients cannot be determined from the SUSY variables.*)
Computec2susyCoefficients[yd_, mypath_List] := Module[
  {expr, myvars, sol},

  expr = CoefficientList[
     (YQa[##, yd] - Getmonic @ EvalQFunction[##]) & @@@ mypath,
     u
  ];
  myvars = Variables[(YQa[##, yd] & @@@ mypath)] /. u -> Nothing;
  sol = Solve[Flatten[expr] == 0, myvars];
  sol[[1]]
]




(* ::Subsection:: *)
(*Compute C-coefficient to SUSY-coefficient (new)*)


QQbbrel[a_, s_]:=Wron[{EvalQFunction[a+1,s+1], EvalQFunction[a,s]}]+EvalQFunction[a+1,s]EvalQFunction[a,s+1]
ComputeYDRegions[yd_List, mP_List] := Module[
  {
    qsys, domain, box, unknowlist, topyd, rightyd
  },
  
  qsys = GenerateQsystem[yd];
  domain = DomainOfInterest;
  box = Tuples[(Range[0, #] &) /@ mP];
  
  unknowlist = Complement[domain, box];
  
 topyd=SortBy[Select[unknowlist,#[[1]]>mP[[1]]&],{#[[1]],-#[[2]]}&];
  rightyd=SortBy[Select[unknowlist,#[[2]]>mP[[2]]&],{-#[[1]],#[[2]]}&];

  
  {topyd, rightyd}
]



QQSolvetop[{A_, S_}] := Module[{a, s},
  a = A - 1;
  s = S;
  EvalQFunction[A, S] =
   ( Wron[
      {EvalQFunction[a + 1, s + 1], EvalQFunction[a, s]}
    ]/EvalQFunction[a, s + 1])//Getmonic//Simplify
]

QQSolveright[{A_, S_}] := Module[{a, s},
  a = A;
  s = S - 1;
  EvalQFunction[A, S] =
   ( Wron[
      {EvalQFunction[a + 1, s + 1], EvalQFunction[a, s]}
    ]/EvalQFunction[a + 1, s])//Getmonic//Simplify
]



ComputesQQDomainOfInterested[yd_List, mP_List] := Module[
  {
    listtoQQsolver,
    domain,
    allSolutionsList = {}
  },
   GenerateSusyWronskian[mP,yd];
   GenerateQsystem[yd];
  (* determine regions for QQ propagation *)
  listtoQQsolver = ComputeYDRegions[yd, mP];
  
  (* initialize endpoints *)
  Do[
    With[{a = ep[[1]], s = ep[[2]]},
      EvalQFunction[a, s] = 1
    ],
    {ep, Endpoints[yd]}
  ];
  
  (* apply right-boundary QQ solvers *)
  Do[
    QQSolveright[list],
    {list, listtoQQsolver[[2]]}
  ];
  
  (* apply top-boundary QQ solvers *)
  Do[
    QQSolvetop[list],
    {list, listtoQQsolver[[1]]}
  ];
  
]



Computec2susyCoefficientsv2[yd_, mP_] := Module[
  {indices, allTaggedEqns, allEqnsOnly, allCVars, knownVars, 
   remainingCVars, selectedPairs, candidates, bestPair, foundVar, 
   finalEqns, cSolution},
  
  (* 1. Generate Indices based on mP (excluding {0,0} if needed, or keeping it) *)
  (* Your code used Rest on the Reverse Tuples, which effectively drops {0,0} *)
 
  indices = (Tuples[Range[0, #] & /@ mP] // Reverse) /. {{0, 0} -> Nothing};

(*
ComputesQQDomainOfInterested[yd, mP];
indices = DomainOfInterest;*)

  (* 2. Generate Equations *)
  allTaggedEqns = Flatten[
    Map[Function[idx,
      (* Generate the equations for this index *)
      eqs = CoefficientList[
        YQa[idx[[1]], idx[[2]], yd] - Getmonic[EvalQFunction[idx[[1]], idx[[2]]]], 
        u
      ];
      (* Tag with index: {{2,0}, equation} *)
      Map[{idx, #} &, eqs]
      ], indices], 1];

  (* 3. Identify ALL 'c' candidates *)
  allEqnsOnly = allTaggedEqns[[All, 2]];
  allCVars = Union[Cases[Variables[allEqnsOnly], c[__]]];

  (* 4. Initialize 'Known' Variables using GenerateSusyWronskian *)
  (* Note: We assume GenerateSusyWronskian is defined in your context *)
  knownVars = Variables[GenerateSusyWronskian[mP, yd][["SusyWronskian"]]] // Rest;
  
  remainingCVars = allCVars;
  selectedPairs = {};

  (* 5. Strict Triangular Sort Loop *)
  While[Length[remainingCVars] > 0,
   
   candidates = Select[allTaggedEqns, Function[taggedItem,
      Module[{eqn, varsInEqn, unknownsInEqn, othersInEqn},
       eqn = taggedItem[[2]];
       varsInEqn = Variables[eqn];
       
       (* Which are 'c' vars we haven't solved yet? *)
       unknownsInEqn = Intersection[varsInEqn, remainingCVars];
       
       (* Which are NOT the unknown 'c'? *)
       othersInEqn = Complement[varsInEqn, unknownsInEqn];
       
       (* CONDITIONS: 
          A. Exactly one unknown c 
          B. Everything else must be in knownVars (or numbers) *)
       Length[unknownsInEqn] == 1 && SubsetQ[knownVars, othersInEqn]
       ]
      ]];
   
   If[candidates === {},
    Print["Stuck! Remaining variables cannot be solved using ONLY known Susy vars."];
    Print["Remaining: ", remainingCVars];
    Break[];
    ];
   
   (* Pick the simplest candidate *)
   bestPair = First[SortBy[candidates, LeafCount[#[[2]]] &]];
   
   (* Add to solution list *)
   AppendTo[selectedPairs, bestPair];
   
   (* Identify the variable we just 'found' *)
   foundVar = First[Intersection[Variables[bestPair[[2]]], remainingCVars]];
   
   (* Mark it as known now *)
   AppendTo[knownVars, foundVar];
   remainingCVars = DeleteCases[remainingCVars, foundVar];
   
   (* Remove equation from pool *)
   allTaggedEqns = DeleteCases[allTaggedEqns, bestPair];
   ];
   If[Length[remainingCVars]==0,Print["\nSuccess! All c-variables are solvable strictly in terms of susyvars."],Print["\nPartial Success. Solved ",Length[allCVars]-Length[remainingCVars]," of ",Length[allCVars]]];


  (* 6. Solve and Return *)
  If[Length[selectedPairs] > 0,
   finalEqns = selectedPairs[[All, 2]];
   cSolution = Solve[finalEqns == 0, allCVars]//Quiet;
   If[cSolution === {}, {}, First[cSolution]], (* Return empty list if no solution *)
   {}
   ];

(*Do[
  With[{a = ep[[1]], s = ep[[2]]},
    EvalQFunction[a, s] = .
  ],
  {ep, Join[Flatten[ComputeYDRegions[yd, mP],1],Endpoints[yd]]}
]//Quiet;*)
cSolution//First
  ];


GetResidualSusySolution[yd_, mP_, mysolution_] := Module[
  {indices, allEqns, residualEqns, remainingVars, finalSolution},
  
  (* Generate all index combinations based on mP *)
  indices = Tuples[Range[0, #] & /@ mP] // Reverse // Rest;
  
  (* Generate all raw equations *)
  allEqns = Flatten[Map[eqnsFor[#, yd, mP] &, indices]];
  
  (* Substitute the known solution and filter for equations that still contain SUSYc *)
  residualEqns = Select[allEqns /. mysolution, ! FreeQ[#, SUSYc] &];
  
  (* Identify the remaining unknown SUSYc variables *)
  remainingVars = Union[Cases[Variables[residualEqns], SUSYc[___][__]]];
  
  (* Solve the residual system *)
  If[remainingVars === {},
   Print["No remaining SUSYc variables found to solve."]; Return[{}],
   finalSolution = Solve[residualEqns == 0, remainingVars];
   If[finalSolution === {}, 
    Print["No solution found for residual variables."]; Return[{}],
    First[finalSolution]
   ]
  ]
];


(* ::Input:: *)
(*(* 2. Generate Equations from Indices *)*)
(*indices = {{2, 0}, {1, 1}, {1, 0}, {0, 1}};*)
(*indices = ( Tuples[Range[0, #] & /@ mP] // Reverse )/.{{0,0}->Nothing};*)
(*allTaggedEqns = Flatten[*)
(*   Map[*)
(*    Function[idx,*)
(*     (* Generate the equations *)*)
(*     eqs = CoefficientList[*)
(*       YQa[idx[[1]], idx[[2]], yd] - Getmonic[EvalQFunction[idx[[1]], idx[[2]]]], *)
(*       u*)
(*     ];*)
(*     (* Tag with index: { {2,0}, equation } *)*)
(*     Map[{idx, #} &, eqs]*)
(*    ],*)
(*    indices*)
(*   ],*)
(*   1*)
(*];*)
(**)
(*(* 3. Identify ALL 'c' candidates *)*)
(*allEqnsOnly = allTaggedEqns[[All, 2]];*)
(*allCVars = Union[Cases[Variables[allEqnsOnly], c[__]]];*)
(**)
(*(* 4. Strict Triangular Sort Logic *)*)
(*(* We start knowing ONLY susyvars. We learn 'c's one by one. *)*)
(*knownVars = Variables[GenerateSusyWronskian[mP,yd][["SusyWronskian"]]]//Rest; *)
(*remainingCVars = allCVars;*)
(*selectedPairs = {};*)
(**)
(*Print["Checking dependencies for ", Length[allCVars], " c-variables..."];*)
(**)
(*While[Length[remainingCVars] > 0,*)
(*   *)
(*   (* CRITICAL CHECK: *)*)
(*   (* 1. Must contain exactly ONE unknown 'c' variable *)*)
(*   (* 2. ALL other variables in the equation must be in 'knownVars' (or numbers) *)*)
(*   *)
(*   candidates = Select[allTaggedEqns, Function[taggedItem,*)
(*      Module[{eqn, varsInEqn, unknownsInEqn, othersInEqn},*)
(*       eqn = taggedItem[[2]];*)
(*       varsInEqn = Variables[eqn];*)
(*       *)
(*       (* Which of these are 'c' vars we haven't solved yet? *)*)
(*       unknownsInEqn = Intersection[varsInEqn, remainingCVars];*)
(*       *)
(*       (* Which are NOT the unknown 'c'? *)*)
(*       othersInEqn = Complement[varsInEqn, unknownsInEqn];*)
(*       *)
(*       (* CONDITIONS: *)*)
(*       (* A. Exactly one unknown c *)*)
(*       Length[unknownsInEqn] == 1 &&*)
(*       (* B. Everything else must be a subset of knownVars *)*)
(*       SubsetQ[knownVars, othersInEqn]*)
(*      ]*)
(*   ]];*)
(*   *)
(*   If[candidates === {}, *)
(*      Print["\nStuck! Remaining variables cannot be solved using ONLY susyvars."];*)
(*      Print["Remaining: ", remainingCVars];*)
(*      Break[]*)
(*   ];*)
(*   *)
(*   (* Pick the simplest candidate *)*)
(*   bestPair = First[SortBy[candidates, LeafCount[#[[2]]] &]];*)
(*   *)
(*   (* Add to solution list *)*)
(*   AppendTo[selectedPairs, bestPair];*)
(*   *)
(*   (* Identify the variable we just 'found' *)*)
(*   foundVar = First[Intersection[Variables[bestPair[[2]]], remainingCVars]];*)
(*   *)
(*   (* Mark it as known now *)*)
(*   AppendTo[knownVars, foundVar];*)
(*   remainingCVars = DeleteCases[remainingCVars, foundVar];*)
(*   *)
(*   (* Remove equation from pool *)*)
(*   allTaggedEqns = DeleteCases[allTaggedEqns, bestPair];*)
(*];*)
(**)
(*(* 5. Display Results *)*)
(*If[Length[remainingCVars] == 0,*)
(*   Print["\nSuccess! All c-variables are solvable strictly in terms of susyvars."],*)
(*   Print["\nPartial Success. Solved ", Length[allCVars] - Length[remainingCVars], " of ", Length[allCVars]]*)
(*];*)
(**)
(*Print["\nSolution Rules:"];*)
(*finalEqns = selectedPairs[[All, 2]];*)
(*cSolution = Solve[finalEqns == 0, allCVars] // First*)


(* ::Subsection::Closed:: *)
(*Compute SUSY-coefficient to C-coefficient (All Q-fuctions)*)


Computesusy2cCoefficientsv2[yd_List, mP_List] := Module[
  {
    listtoQQsolver,
    domain,
    allSolutionsList = {}
  },
   GenerateSusyWronskian[mP,yd];
   GenerateQsystem[yd];
  (* determine regions for QQ propagation *)
  listtoQQsolver = ComputeYDRegions[yd, mP];
  
  (* initialize endpoints *)
  Do[
    With[{a = ep[[1]], s = ep[[2]]},
      EvalQFunction[a, s] = 1
    ],
    {ep, Endpoints[yd]}
  ];
  
  (* apply right-boundary QQ solvers *)
  Do[
    QQSolveright[list],
    {list, listtoQQsolver[[2]]}
  ];
  
  (* apply top-boundary QQ solvers *)
  Do[
    QQSolvetop[list],
    {list, listtoQQsolver[[1]]}
  ];
  
  (* reverse evaluation order inside the domain *)
  domain = DomainOfInterest // Reverse;
  
  (* iterative local solving *)
  Do[
    Module[{pt, eqs, vars, sol},
      
      pt = domain[[k]];
      
      eqs  = eqnsFor[pt, yd, mP][[1]] /. allSolutionsList;
      vars = varsFor[pt, yd, mP];
      
      sol = Solve[eqs == 0, vars] // First // Quiet;
      
      allSolutionsList = Join[allSolutionsList, sol];
    ],
    {k, Length[domain]}
  ];
  
  allSolutionsList
]



(* ::Input:: *)
(*listtoQQsolver=ComputeYDRegions[yd,mP]*)
(*Do[*)
(*  With[{a = ep[[1]], s = ep[[2]]},*)
(*    EvalQFunction[a, s] = 1*)
(*  ],*)
(*  {ep, Endpoints[yd]}*)
(*];*)
(**)
(*Do[*)
(*QQSolveright[list],*)
(*{list,listtoQQsolver[[2]]}*)
(*]*)
(*Do[*)
(*QQSolvetop[list],*)
(*{list,listtoQQsolver[[1]]}*)
(*]*)
(**)
(**)
(**)
(*domain = DomainOfInterest // Reverse;*)
(**)
(*allSolutionsList = {};   (* list of accumulated replacement rules *)*)
(**)
(*Do[*)
(*  Module[{pt = domain[[k]], eqs, vars, sol},*)
(*   *)
(*   (* substitute all previously obtained rules *)*)
(*   eqs  = eqnsFor[pt, yd, mP][[1]] /. allSolutionsList;*)
(*   vars = varsFor[pt, yd, mP];*)
(*   *)
(*   (* solve current local equation *)*)
(*   sol = Solve[eqs == 0, vars] // First//Quiet;*)
(*   *)
(*   (* append rules to the cumulative list *)*)
(*   allSolutionsList = Join[allSolutionsList, sol];*)
(*  ],*)
(* {k, Length[domain]}*)
(*];*)
(**)


(* ::Subsection::Closed:: *)
(*Compute SUSY-coefficient to C-coefficient ( Only up to mP)*)


(* Function Definition *)
Computesusy2cCoefficientsv3[yd_, mP_] := Module[
  {indices, allEqns, remainingVars, candidates, bestEq, foundVar, selectedEqs, solution},
  (* 1. Generate all index combinations based on mP *)
  indices = Tuples[Range[0, #] & /@ mP] // Reverse // Rest;
  
  (* 2. Map eqnsFor over those indices to get all equations *)
  allEqns = Flatten[Map[eqnsFor[#, yd, mP] &, indices]];
  
  
  (* 4. Automatic Selection Logic (Triangular Sort) *)
  selectedEqs = {};
  remainingVars = Variables[GenerateSusyWronskian[mP,yd][["SusyWronskian"]]]//Rest;
(*    remainingVars = Variables[allEqns]/.{sym[___]->Nothing,c[a__,b__,c__]->Nothing};

*)
  While[Length[remainingVars] > 0,
   (* Find equations that contain exactly ONE of the remaining unknown variables *)
   candidates = Select[allEqns, Count[Variables[#], _?(MemberQ[remainingVars, #] &)] == 1 &];
   
   If[candidates === {},
    Print["System is coupled (not triangular). Cannot auto-sort further."];
    Return[$Failed]; (* Exit if stuck *)
   ];
   
   (* Pick the smallest/simplest candidate equation *)
   bestEq = First[SortBy[candidates, LeafCount]];
   
   (* Add to our solved list *)
   AppendTo[selectedEqs, bestEq];
   
   (* Identify which variable this equation solves *)
   foundVar = First[Intersection[Variables[bestEq], remainingVars]];
   
   (* Remove that variable from the 'unknowns' list *)
   remainingVars = DeleteCases[remainingVars, foundVar];
  ];
  
  (* 5. Solve and Return *)
  (* We use First to get the rule list {v1->val, v2->val} instead of {{...}} *)
  solution = Solve[selectedEqs == 0, susyvars];
  
  If[solution === {}, 
   Print["No solution found."]; Return[{}],
   Return[First[solution]]
  ]
];


(* ::Input:: *)
(*(* 1. Generate all index combinations based on mP *)*)
(*indices = Tuples[Range[0, #] & /@ mP] // Reverse // Rest;*)
(**)
(*(* 2. Generate equations WITH Source Index AND List Position *)*)
(*(* Structure: { {source_index}, position_index, equation } *)*)
(*allTaggedEqns = Flatten[*)
(*   Map[*)
(*    Function[idx,*)
(*     (* Get the list of equations for this index *)*)
(*     rawEqs = eqnsFor[idx, yd, mP];*)
(*     (* Tag each equation with the index 'idx' and its position 'pos' *)*)
(*     MapIndexed[{idx, First[#2], #1} &, rawEqs]*)
(*     ],*)
(*    indices*)
(*    ],*)
(*   1];*)
(**)
(*(* 3. Automatic Selection Logic *)*)
(*selectedTriplets = {};*)
(*remainingVars = susyvars;*)
(**)
(*While[Length[remainingVars] > 0,*)
(*   *)
(*   (* LOOK AT PART 3 (#[[3]]) for the equation content *)*)
(*   candidates = Select[allTaggedEqns, *)
(*     Count[Variables[#[[3]]], _?(MemberQ[remainingVars, #] &)] == 1 &*)
(*     ];*)
(*   *)
(*   If[candidates === {}, *)
(*    Print["System is coupled (not triangular). Cannot auto-sort further."]; *)
(*    Break[]*)
(*    ];*)
(*   *)
(*   (* Sort by complexity of the equation (Part 3) *)*)
(*   bestTriplet = First[SortBy[candidates, LeafCount[#[[3]]] &]];*)
(*   *)
(*   (* Store the whole triplet *)*)
(*   AppendTo[selectedTriplets, bestTriplet];*)
(*   *)
(*   (* Identify which variable this equation solves *)*)
(*   foundVar = First[Intersection[Variables[bestTriplet[[3]]], remainingVars]];*)
(*   *)
(*   (* Remove that variable from the 'unknowns' list *)*)
(*   remainingVars = DeleteCases[remainingVars, foundVar];*)
(*   *)
(*   (* Optional: Remove the selected equation from the pool *)*)
(*   allTaggedEqns = DeleteCases[allTaggedEqns, bestTriplet];*)
(*   ];*)
(**)
(*(* 4. Display Logic *)*)
(*Print["Automatically Selected Equations (Source -> Equation):"];*)
(**)
(*(* Create a readable table *)*)
(*Grid[*)
(* Map[*)
(*  Function[item,*)
(*   {*)
(*    (* Format: eqnsFor[{2,0}][[1]] *)*)
(*    Row[{"eqnsFor[", item[[1]], "][[", item[[2]], "]]"}], *)
(*    " \[RightArrow] ", *)
(*    item[[3]] (* The Equation *)*)
(*    }*)
(*   ], *)
(*  selectedTriplets*)
(*  ],*)
(* Frame -> All, Alignment -> {Left, Center}*)
(* ]*)
(**)
(*(* 5. Solve *)*)
(*finalEqns = selectedTriplets[[All, 3]]; (* Extract just the equations *)*)
(*solution = Solve[finalEqns == 0, susyvars];*)


(* ::Subsection::Closed:: *)
(*QQ-relations*)


(*Eq. 5.8*)
QQbbrel[a_, s_]:=Wron[{Qbb[a+1,s+1] ,Qbb[a,s]}]-Qbb[a+1,s]Qbb[a,s+1]
(*Distingulish Q-functions*)
Qbb[a_, s_] := Q[Range[a + 1, mP[[1]]], Range[s + 1, mP[[2]]]]
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


(* ::Subsection::Closed:: *)
(*Reduce Q-functions*)


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

  tmp /. {Qlocal -> Q,Wronlocal->Wron}/.localwQQb//Simplify
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



(* ::Subsection::Closed:: *)
(*Grassmannian*)


ClearAll[Qasy]
Qasy[w_, b_] := 
  1/(w! b!) *
   Sum[
       Qlocal[
         Table[Subscript[a, i], {i, 1, w}],
         Table[Subscript[i, q], {q, 1, b}]
     ] *
     Dot @@ Table[Subscript[\[Psi], 0]^Subscript[a, i], {i, 1, w}] *
     Dot @@ Table[Subscript[\[Psi], 1]^Subscript[i, q], {q, 1, b}],
     Evaluate[Sequence @@ Table[{Subscript[a, i], 1, mP[[1]]}, {i, w}]],
     Evaluate[Sequence @@ Table[{Subscript[i, q], 1, mP[[2]]}, {q, b}]]
   ];

removeRepeated = Qlocal[a_List, b_List] /; (DuplicateFreeQ[a] && DuplicateFreeQ[b]) :> Qlocal[a, b];

killRepeated = Qlocal[a_List, b_List] /; Not[DuplicateFreeQ[a] && DuplicateFreeQ[b]] :> 0;
shiftu[int_]:=u->u+int I /2


(* ::Section::Closed:: *)
(*Old Functions*)


MfromLambda[lambda_List] := Module[{N},
  N = Length[lambda];
  Table[
    Total[lambda[[a + 1 ;; N]]],
    {a, 1, N - 1}
  ]
]

ProjectYoungDiagram[yd_List,mP:{a_,b_}]:=DeleteCases[Max[#,0]&/@(Take[yd,a]-b),0]
TransposeProjectYoungDiagram[yd_List, mP : {a_, b_}] :=
 Module[{ydT},
  ydT =TransposeYoungD[yd];
  DeleteCases[Max[#, 0] & /@ (Take[ydT, a] - b), 0]
 ]


Computesusy2cCoefficients[yd_,KDpath_,mP_] := Module[
  {ssols = {}, subs = {},node, as, inds, sol,index},
 
  index = susyPointOfInterested[yd,KDpath,mP];
  Do[
    node = index[[k]];
    as   = node[[1]];     (* {a,s} *)
    inds = node[[2]];     (* list of indices *)

    sol = Quiet[Solve[
      (eqnsFor[as,yd,mP] /. subs)[[inds]] == 0,
      varsFor[as,yd,mP]
    ], Solve::svars] // First;

    ssols = Append[ssols, sol];
    subs = Join[subs, sol];

    ,
    {k, Length[index]}
  ];

  ssols//Flatten
]




Bdegs[yd_]:=Block[{bosdeg},{bosdeg=(Reverse[yd]+Range[0,Length@yd-1]),Complement[Range[0,bosdeg//Max],bosdeg]}]
susyPointOfInterested[yd_, path_,mP_] := Module[
  {l, d, n, a, s, maxD, bosdeg, raw, cleaned, k},

  bosdeg = Bdegs[yd][[1]];

  raw = Table[
    {a, s} = p;

    l = Length[yd] - a - s;
    If[l <= 0,
      Nothing, (* skip *)
      d =  bosdeg[[;; -(a + s) - 1]];
      maxD = Max[d];
      n = Complement[Range[0, maxD], d];

      {p, Total[d[[;; -2]]] + n - l (l - 1)/2 + 1}
    ],
    {p, path}
  ];

  cleaned = DeleteCases[raw, Nothing];

  k = (Flatten[cleaned[[All, 2]]] // Length) - Total[yd];
  If[k<0, cleaned[[1,2]]=Range[Length@eqnsFor[cleaned[[1,1]],yd,mP]]];
  (* return both *)
(*  <|
    "Points" -> cleaned,
    "k" -> k,
    "test"->If[k<0, cleaned[[1,2]]=Range[Length@eqnsFor[cleaned[[1,1]],yd,mP]]]
  |>;*)
  cleaned
]

