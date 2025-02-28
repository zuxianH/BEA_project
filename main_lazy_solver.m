(* ::Package:: *)

(* ::Subsection::Closed:: *)
(*Standard commands*)


mult[\[Lambda]_] := 
  Plus @@ \[Lambda]! / \!\(
\*UnderoverscriptBox[\(\[Product]\), \(a = 0\), \(Length[\[Lambda]] - 1\)]
\*FractionBox[\(\((\[Lambda][\([Length[\[Lambda]] - a]\)] + a)\)!\), \(
\*UnderoverscriptBox[\(\[Product]\), \(k = 0\), \(\(-1\) + a\)]\((a - k + \[Lambda][\([\(-a\)]\)] - \[Lambda][\([\(-k\)]\)])\)\)]\);
(*Computes the conjugate (transpose) of a Young tableau.*)
DualDiagram[\[Lambda]_] := Total /@ Transpose[(PadRight[#1, \[Lambda][[1]]] & ) /@(ConstantArray[1, #1] & ) /@ \[Lambda]]; 

(*Converts standard Young tableau to its shape*)
ToYD[stb_]:=Length/@stb;

(*Validates if a Young tableau is standard. Output False or True*)
CheckStandard[\[Lambda]T_] := 
  And @@ Flatten[{
    Table[\[Lambda]T[[a - 1, s]] < \[Lambda]T[[a, s]], 
      {a, 2, Length[\[Lambda]T]}, {s, 1, Length[\[Lambda]T[[a]]]}], 
    
    Table[\[Lambda]T[[a, s - 1]] < \[Lambda]T[[a, s]], 
      {a, 1, Length[\[Lambda]T]}, {s, 2, Length[\[Lambda]T[[a]]]}], 
    
    Sort[Flatten[\[Lambda]T]] == Range[Length[Flatten[\[Lambda]T]]], 
    
    ListQ /@ \[Lambda]T
  }];



(* ::Input:: *)
(*CheckStandard[{{1, 2, 4}, {3, 5, 6}}]*)


(*Computes the Wronskian determinant of two polynomials*)
Wronsk[A_, B_] := (A /. u -> u + I/2)*(B /. u -> u - I/2) - (A /. u -> u - I/2)*(B /. u -> u + I/2); 

(*convert poly to monic*)
toMonic[A_] := Collect[ (#1/Coefficient[#1, u, Exponent[#1, u]] & )[ Expand[A]], u]; 


(* ::Input:: *)
(*toMonic[2u^2+3]*)


mPrint[x___]:=Print[x];
PrintDone[x_]:=mPrint["...Done in: ",Timing[x][[1]],"s"];
SetAttributes[PrintDone,HoldAll];

mPrint[x_]:=Null;


(* ::Subsection::Closed:: *)
(*Q-system on Young diagram*)


(* ::Text:: *)
(*GenerateQsystem generates all QQ-relations. Input is  \[Lambda] - a Young diagram, you can also tinker with the code and specify Domain of interest (collection of {a,s} specifying which QQ-relations to take into account). The other code is compatible with this specification. *)


GenerateQsystem[\[Lambda]_]:=Block[{},
(mPrint["Generating QQ relations on Young diagram..."];
(* Length of spin chain *)
Len=Total[\[Lambda]];
Unprotect[M];ClearAll[M];(* Unprotecting because of conflict with Combinatorica package *)
(* domain of interest is the values of {a,s} for which we are going to check QQ relation with Q[a,s] in the top left corner (smallest a,s)
FullYoungDiagram - is maximal possible domain of interest*)
FullYoungDiagram=Block[{mm},Flatten@Table[mm[a,s],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}]/.mm->List];
DomainOfInterest=FullYoungDiagram;
(* comment below provides some example of non-standard DomainOfInterest *)
(*DomainOfInterest=Block[{mm},Flatten@Table[mm[a,s],{a,0,1},{s,0,1}]/.mm\[Rule]List];*)
M[a_,s_]:=M[a,s]=Len+a s-Total[\[Lambda][[1;;a]]]-Total[DualDiagram[\[Lambda]][[1;;s]]];
YQa[0,0]:=u^Len+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k\), \(Len\)]\(
\*SuperscriptBox[\(u\), \(Len - k\)]\ sym[k]\)\);
YQa[a_,s_]:=u^M[a,s]+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k\), \(M[a, s]\)]\(c[a, s, k]\ 
\*SuperscriptBox[\(u\), \(M[a, s] - k\)]\)\);
YQ\[Theta][0,0]=YQa[0,0];
YQ\[Theta][a_,s_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(k = 1\), \(M[a, s]\)]\((u - q\[Theta][a, s, k])\)\);
QQrel[a_,s_]:=
CoefficientList[(YQa[a,s]/.u->u+I/2)(YQa[a+1,s+1]/.u->u-I/2)-(YQa[a,s]/.u->u-I/2)(YQa[a+1,s+1]/.u->u+I/2)-I(M[a,s]-M[a+1,s+1])YQa[a+1,s]YQa[a,s+1],u]//(#/.Complex[0,b_]:>b)&;
Allrel=Monitor[Table[If[MemberQ[DomainOfInterest,{a,s}]&&M[a,s]>0,QQrel[a,s],Nothing],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}],{a,s}]//Flatten;
(* vars have coefficients of all Q-functions *)
vars=Table[If[a+s==0,Nothing,c[a,s,k]],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1},{k,M[a,s]}]//Flatten;
(* only those appearing in domain of interest *)
vars2=DeleteCases[Variables[Allrel],sym[_]];
mPrint@Column[{
Row@{"Length of spin chain: ",Len},
Row@{"Number of SYT: ",mult[\[Lambda]]},
Row@{"Domain of Interest: ",MatrixPlot[#,Mesh->True]&@Table[Which[MemberQ[DomainOfInterest,{a,s}],1,MemberQ[FullYoungDiagram,{a,s}],1/2,True,0],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[1]]-1}]},
Row@{"Number of variables: ",Length[vars2]},
Row@{"Number of equations: ",Length[Allrel]}
}];
)//PrintDone
];


(* ::Input:: *)
(*GenerateQsystem[{4,2,1}]*)
(*MatrixPlot[Table[Which[MemberQ[DomainOfInterest,{a,s}],1,MemberQ[FullYoungDiagram,{a,s}],1/2,True,0],{a,0,Length[{4,2,1}]-1},{s,0,{4,2,1}[[1]]-1}],Mesh->True]*)
(*Allrel  (*Stores all QQ-relations*)*)
(*vars2  (*Stores all variables used*)*)


(* ::Input:: *)
(*vars2//MatrixForm*)


(* ::Subsection::Closed:: *)
(*Choice of SYT and initial conditions*)


(* ::Text:: *)
(*showSYT will draw SYT with \[Lambda]T as global area. Shaded region is decided domain of interest*)


showSYT[\[Lambda]T_] := Graphics[
  Table[
    {
      Text[Style[\[Lambda]T[[a, s]], Small, Black], {s, -a}], 
      Opacity[0.5], 
      Lighter[Lighter[Gray]], 
      Rectangle[{s - 1/2, -a - 1/2}]
    }, 
    {a, 1, Length[\[Lambda]T]}, 
    {s, 1, Length[\[Lambda]T[[a]]]}
  ], 
  ImageSize -> Tiny
];

(* Next command includes domain of interest *)
showSYT[\[Lambda]T_, "DOI"] := Graphics[
  Table[
    {
      Text[Style[\[Lambda]T[[a, s]], Small, Black], {s, -a}],
      Opacity[0.5],
      Lighter[Lighter[Gray]],
      Rectangle[{s - 1/2, -a - 1/2}],
      If[
        MemberQ[DomainOfInterest, {a - 1, s - 1}],
        {Gray, Rectangle[{s - 1/2, -a - 1/2}]},
        Nothing
      ]
    },
    {a, 1, Length[\[Lambda]T]},
    {s, 1, Length[\[Lambda]T[[a]]]}
  ],
  ImageSize -> Tiny
];



(* ::Input:: *)
(*showSYT[{{1, 2, 4,7}, {3, 5, 6}}]*)


(* ::Subsection::Closed:: *)
(*init\[Theta]rep*)


(* ::Text:: *)
(*Solution of Q-system in the large \[CapitalLambda] limit, the leading order*)


init\[Theta]rep[\[Lambda]T_] := init\[Theta]rep[\[Lambda]T] = 
  Block[{kk, sd}, 
    
    kk[_, _] = 0; 
    sd[m_] := (Select[#1, #1 <= m &] &) /@ \[Lambda]T; 
    
    If[CheckStandard[\[Lambda]T], 
      
      Sort[Flatten[
        Table[
          Table[
            If[True || MemberQ[DomainOfInterest, {a2, s2}], 
              q\[Theta][a2, s2, ++kk[a2, s2]] -> 
                \!\(
\*UnderoverscriptBox[\(\[Product]\), \(a3 = 1\), \(a2\)]\(
\*FractionBox[\(Length[\(sd[\[Lambda]T[\([a, s]\)]]\)[\([a3]\)]] + a - s - a3\), \(Length[\(sd[\[Lambda]T[\([a, s]\)]]\)[\([a3]\)]] + a - s - a3 + 1\)]*\(
\*UnderoverscriptBox[\(\[Product]\), \(s3 = 1\), \(s2\)]
\*FractionBox[\(\(DualDiagram[Length /@ sd[\[Lambda]T[\([a, s]\)]]]\)[\([s3]\)] + s - a - s3\), \(\(DualDiagram[Length /@ sd[\[Lambda]T[\([a, s]\)]]]\)[\([s3]\)] + s - a - s3 + 1\)]*\[Theta][\[Lambda]T[\([a, s]\)]]\)\)\), 
              Nothing
            ], 
            {a2, 0, a - 1}, {s2, 0, s - 1}
          ], 
          {a, 1, Length[\[Lambda]T]}, {s, 1, Length[\[Lambda]T[[a]]]}
        ]
      ]], 
      
      Print["Not standard tableau"];
    ]
  ];




(* ::Input:: *)
(*init\[Theta]rep[{{1, 2, 4}, {3, 5, 6}}]*)


(* ::Subsection:: *)
(*Large\[CapitalLambda]Expansion*)


(* ::Text:: *)
(*Generating system of relations with leading coefficient plugged in. Working only up to maxord (I think I overdo one order)*)


Large\[CapitalLambda]Expansion := Block[{},
  
  (* Print initial message and display the SYT solution *)
  mPrint["1/\[CapitalLambda] expansion of QQ system around the chosen SYT solution..."];
  showSYT[\[Lambda]T] // mPrint;
  
  (* Initialize \[Theta] representation with \[CapitalLambda] expansion *)
  \[CapitalLambda]init\[Theta]rep = init\[Theta]rep[\[Lambda]T] /. \[Theta][i_] :> \[CapitalLambda]^i;
  
  (* Compute fsym representation *)
  fsymrep = Table[
    sym[n] -> Expand @ Coefficient[
      Product[u - \[CapitalLambda]^i, {i, Len}], 
      u, Len - n
    ],
    {n, Len}
  ];
  
  (* Definition for forward compatibility *)
  finit\[Theta]rep = \[CapitalLambda]init\[Theta]rep;
  
  (* Solve for ftransit *)
  ftransit = Solve[
    (Table[
      If[a + s == 0 || Not @ MemberQ[vars2, c[a, s, 1]], 
        Nothing, 
        CoefficientList[
          YQa[a, s] - (YQ\[Theta][a, s] /. \[CapitalLambda]init\[Theta]rep), 
          u
        ]
      ],
      {a, 0, Length[\[Lambda]] - 1}, 
      {s, 0, \[Lambda][[a + 1]] - 1}
    ] // Flatten) == 0,
    vars2
  ][[1]];
  
  (* Define the transition rule for \[CapitalLambda] *)
  \[CapitalLambda]transit = Thread[
    Rule[
      ftransit[[All, 1]],
      (# /. \[CapitalLambda]^(pow_ /; pow < Exponent[#, \[CapitalLambda]] - maxord) :> 0) & /@ ftransit[[All, 2]]
    ]
  ];
  
  (* Choosing special parameterization of inhomogeneities *)
  symrep = Table[
    sym[n] -> Expand @ Coefficient[
      Product[u - \[CapitalLambda]^i, {i, Len}], 
      u, Len - n
    ] /. \[CapitalLambda]^(pow_ /; pow < n/2 (2 Len - n + 1) - maxord) :> 0,
    {n, Len}
  ];
  
  (* Compute and collect analytic expressions *)
  anlytic = Collect[
    (Allrel /. symrep /. c[a_, s_, k_] :> (1 + ecc[a, s, k]/\[CapitalLambda]) c[a, s, k] /. \[CapitalLambda]transit) // Expand, 
    \[CapitalLambda]
  ];
  
] // PrintDone;

(* Check if the generated equations are correct *)
"Check on generated equations: " If[
  ((Exponent[anlytic, \[CapitalLambda]] // Min) > 0), 
  "passed"
] // mPrint;









(* ::Input:: *)
(*\[Lambda]T={{1, 2, 4}, {3, 5, 6}}*)
(*GenerateQsystem[{4,2,1}];*)
(*Large\[CapitalLambda]Expansion*)
(*symrep*)
(**)


(* ::Subsection:: *)
(*SubleadingOrders*)


(* ::Text:: *)
(*Generating list of subleading equations and solving them.*)


SubleadingOrders := Block[{},
  
  mPrint["Arranging and solving 1/\[CapitalLambda] analytic equations for c..."];
  
  sublead = Monitor[
    Table[
      Normal@Series[
        (#/\[CapitalLambda]^Exponent[#, \[CapitalLambda]]) &[anlytic[[k]]],
        {\[CapitalLambda], \[Infinity], maxord}
      ],
      {k, Length[anlytic]}
    ],
    k
  ];
  
  cutoff = Series[\[CapitalLambda], {\[CapitalLambda], \[Infinity], maxord - 1}] - \[CapitalLambda];
  
  subleadingeqns = Monitor[
    Table[
      (sublead[[k]] /. ecc[a_, s_, k_] :> 
        Sum[ecc[ord][a, s, k]/\[CapitalLambda]^(ord - 1), {ord, 1, maxord}] + cutoff)[[3]],
      {k, Length[sublead]}
    ],
    k
  ];
  
  Do[
    \[CapitalLambda]sol[ord] = Solve[
      subleadingeqns[[All, ord]] == 0 /. Flatten@Table[\[CapitalLambda]sol[k], {k, ord - 1}],
      vars2 /. c[a_, s_, k_] :> ecc[ord][a, s, k]
    ][[1]],
    {ord, maxord}
  ];
  
] // PrintDone;


SubleadingOrders:=Block[{},
(mPrint["Arranging and solving 1/\[CapitalLambda] analytic equations for c..."];
sublead=Monitor[Table[Normal@Series[(#/\[CapitalLambda]^Exponent[#,\[CapitalLambda]])&[anlytic[[k]]],{\[CapitalLambda],\[Infinity],maxord}],{k,Length[anlytic]}],k];
cutoff=Series[\[CapitalLambda],{\[CapitalLambda],\[Infinity],maxord-1}]-\[CapitalLambda];
subleadingeqns=Monitor[Table[(sublead[[k]]/.ecc[a_,s_,k_]:>Sum[ecc[ord][a,s,k]/\[CapitalLambda]^(ord-1),{ord,1,maxord}]+cutoff)[[3]],{k,Length[sublead]}],k];
Do[\[CapitalLambda]sol[ord]=Solve[subleadingeqns[[All,ord]]==0/.Flatten@Table[\[CapitalLambda]sol[k],{k,ord-1}],vars2/.c[a_,s_,k_]:>ecc[ord][a,s,k]][[1]],{ord,maxord}];
;)//PrintDone
]



\[Lambda]T={{1, 2, 4}, {3, 5, 6}}
GenerateQsystem[{4,2,1}];
Large\[CapitalLambda]Expansion
symrep
SubleadingOrders


(* ::Subsection:: *)
(*GenerateEqnsForNumerics*)


GenerateEqnsForNumerics := Block[{},
  
  mPrint["Generating equations for numerical iterations"];
  
  (* Define normalized variables and transformation rules *)
  nvars = vars2 /. c -> nc;
  
  (* Define transformations between sym and nsym variables *)
  sym2nsym = Table[
    sym[n] -> \[CapitalLambda]^(n (2 Len - n + 1)/2) nsym[n], 
    {n, Len}
  ];
  
  nsym2sym = Table[
    nsym[n] -> \[CapitalLambda]^(-n (2 Len - n + 1)/2) sym[n], 
    {n, Len}
  ];
  
  (* Transform variables to normalized variables *)
  vars2nvars = Thread[
    Rule[
      vars2, 
      vars2 /. c[a_, s_, k_] :> (\[CapitalLambda]^Exponent[c[a, s, k] /. ftransit, \[CapitalLambda]] nc[a, s, k])
    ]
  ];
  
  (* Transform back from normalized variables to original variables *)
  nvars2vars = Thread[
    Rule[
      nvars, 
      vars2 /. c[a_, s_, k_] :> (\[CapitalLambda]^(-Exponent[c[a, s, k] /. ftransit, \[CapitalLambda]]) c[a, s, k])
    ]
  ];
  
  (* Rescale fsym equations *)
  nfsymrep = Thread[
    Rule[
      fsymrep[[All, 1]] /. sym -> nsym, 
      Collect[
        (# \[CapitalLambda]^-Exponent[#, \[CapitalLambda]] &) /@ fsymrep[[All, 2]], 
        \[CapitalLambda]
      ]
    ]
  ];
  
  (* Rescale ftransit equations *)
  nftransit = Thread[
    Rule[
      ftransit[[All, 1]] /. c -> nc, 
      Collect[
        (# \[CapitalLambda]^-Exponent[#, \[CapitalLambda]] &) /@ ftransit[[All, 2]], 
        \[CapitalLambda]
      ]
    ]
  ];
  
  (* Compute the rescaled version of the equations *)
  NormedEqns = Collect[
    (# \[CapitalLambda]^-Exponent[#, \[CapitalLambda]] &) /@ (Allrel /. vars2nvars /. sym2nsym), 
    \[CapitalLambda]
  ];
  
] // PrintDone;


(* ::Subsection:: *)
(*AsymEqns*)


(* Generating equations using asymptotic approximation *)
AsymEqns[\[CapitalLambda]0_] := Block[{},
  
  (* Substitute \[CapitalLambda] with the given value *)
  nsymrep = nfsymrep /. \[CapitalLambda] -> \[CapitalLambda]0;
  ntransit = nftransit /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Define the transformation for nc variables using asymptotic expansion *)
  subnc = Thread[
    Rule[
      nvars, 
      nvars /. (nc[a_, s_, k_] :> (1 + 1/\[CapitalLambda]0 Sum[
        1/\[CapitalLambda]0^(ord - 1) (ecc[ord][a, s, k] /. \[CapitalLambda]sol[ord]), 
        {ord, 1, maxord}
      ]) nc[a, s, k]) /. ntransit
    ]
  ];
  
  (* Apply normalization and expansion *)
  #/(1 + Abs[# /. nc[a_, s_, k_] :> (nc[a, s, k] /. subnc)]) & /@ 
    (NormedEqns /. nsymrep /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand
];

(* Generating equations using previous order results and polynomial fit *)
InterpEqns[\[CapitalLambda]0_] := Block[{minterpord = Min[Length[\[CapitalLambda]vals] - 1, interpord]},
  
  (* Substitute \[CapitalLambda] with the given value *)
  nsymrep = nfsymrep /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Compute interpolated subnc values using polynomial fitting *)
  subnc = Thread[
    Rule[
      nvars, 
      Round[
        Sum[
          (nvars /. sol[\[CapitalLambda]vals[[-j]]]) 
            Product[
              If[j == j2, 1, (\[CapitalLambda]0 - \[CapitalLambda]vals[[-j2]]) / (\[CapitalLambda]vals[[-j]] - \[CapitalLambda]vals[[-j2]])], 
              {j2, minterpord}
            ],
          {j, minterpord}
        ], 
        10^-prec
      ]
    ]
  ];
  
  (* Normalize and expand the equations *)
  # / (# /. nc[a_, s_, k_] :> ((1 + Round[Random[]/100, 10^-5]) nc[a, s, k] /. subnc)) & /@ 
    (NormedEqns /. nsymrep /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand
];

(* Routine to produce solution *)
FindSolit := (
  i = 0;
  {minim, minsolrep} = Monitor[
    FindMinimum[
      normedrel . normedrel, 
      {nvars, nvars /. subnc} // Transpose,
      WorkingPrecision -> prec, 
      PrecisionGoal -> Infinity, 
      AccuracyGoal -> prec/2, 
      MaxIterations -> 50, 
      Method -> Automatic, 
      EvaluationMonitor :> (
        i++;
        norm = normedrel . normedrel // N;
        If[i > MyMaxIterations, Throw["Too big step"]]
      )
    ], 
    Row[{"Step: ", i, ",   Minim: ", norm}]
  ]
);

SilentFindSolit := (
  i = 0;
  {minim, minsolrep} = FindMinimum[
    normedrel . normedrel, 
    {nvars, nvars /. subnc} // Transpose, 
    WorkingPrecision -> prec, 
    PrecisionGoal -> Infinity, 
    AccuracyGoal -> prec/2, 
    MaxIterations -> 50, 
    Method -> Automatic, 
    EvaluationMonitor :> (
      i++; 
      If[i > MyMaxIterations, Throw["Too big step"]]
    )
  ]
);



(* ::Subsection:: *)
(*SolveAt\[CapitalLambda]0*)


(* Solving first point solution to decide where to start *)
SolveAt\[CapitalLambda]0 := Block[{},
  
  mPrint["Checking if can solve at \[CapitalLambda]0. If this produces mistakes, increase \[CapitalLambda]0"];
  
  (* Initialize iteration counter *)
  i = 0;
  
  (* Generate normalized equations using asymptotic approximation at \[CapitalLambda]0 *)
  normedrel = AsymEqns[\[CapitalLambda]0];
  
  (* Solve the system *)
  FindSolit;
  
  (* Print the numerical value of the minimized solution *)
  minim // N // mPrint;
];



(* ::Subsection:: *)
(*GenerateSolsFromAsymptotics*)


(* Generating first sample points for interpolation + some large \[CapitalLambda] expressions *)
GenerateSolsFromAsymptotics := Block[{},
  
  mPrint["Initialize: Numerical solutions from analytic 1/\[CapitalLambda] approximation"];
  
  (* Initialize the list of \[CapitalLambda] values *)
  \[CapitalLambda]vals0 = {};
  
  (* Define a range of \[CapitalLambda] values for solving *)
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;
  
  (* Iterate over the range and compute solutions *)
  Monitor[
    Do[
      (* Generate normalized equations using asymptotic approximation *)
      normedrel = AsymEqns[\[CapitalLambda]0];
      
      (* Solve the system *)
      FindSolit;
      
      (* Store the solution *)
      sol[\[CapitalLambda]0] = minsolrep;
      
      (* Append the current \[CapitalLambda] value to the list *)
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];
      
      , {\[CapitalLambda]0, rng}
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}]
  ];
  
] // PrintDone;



(* ::Subsection:: *)
(*GenerateSolsFromAsymptotics*)


(* Iteration procedure *)
Iterateit := Block[{},
  
  mPrint["Numerical iterations towards \[CapitalLambda] = ", \[CapitalLambda]target];
  mPrint["If step becomes below \!\(\*SuperscriptBox[\(10\), \(-7\)]\), try to increase precision"];
  
  (* Initialize step parameters *)
  pp = pmin;
  qq = 1;
  step := qq / base^pp;
  
  (* Start the iteration procedure *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
  
  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,
      
      (* Compute the new \[CapitalLambda] value *)
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
      
      (* Generate equations using interpolation *)
      normedrel = InterpEqns[\[CapitalLambda]new];
      
      (* Solve equations and handle step size adjustments *)
      Which[
        Catch[SilentFindSolit] === "Too big step",
          pp = pp + 1,
        
        i > 5,
          sol[\[CapitalLambda]new] = minsolrep;
          AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new],
        
        True,
          sol[\[CapitalLambda]new] = minsolrep;
          AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];
          
          (* Adjust step size dynamically *)
          If[pp > pmin,
            qq = qq + \[CapitalDelta]q;
            If[qq == base, qq = 1; pp = pp - 1];
          ]
      ];
      
      (* Update last \[CapitalLambda] value *)
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
      
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
  ] // PrintDone;
  
  (* Print final status message *)
  mPrint["Finished iterations. List of all \[CapitalLambda] computed: ", \[CapitalLambda]vals // N];
];



(* ::Subsection:: *)
(* Relating to rigged configurations Inits*)


(*Load Rigged Configurations Package*)
SetDirectory[NotebookDirectory[]];
<<RC.m;

(*Path\[LeftRightArrow]Tableaux Conversions*)

(*Convert a standard Young tableau (SYT) to a crystal path representation*)
ToCrystalPath[stb_]:=Block[{len=Length[stb//Flatten]},Table[{{Position[stb,k][[1,1]]}},{k,len}]];

(*Convert a crystal path back into a tableau*)
ToTableau[path_]:=Block[{pr=path//Flatten,max},max=Max[pr];
Table[Position[pr,k]//Flatten,{k,max}]];

(*Load necessary package for combinatorial operations*)
Quiet[Needs["Combinatorica`"]];

(*Generate a rigged configuration from a standard Young tableau (SYT)*)
ToRigged[SYT_,n_:5]:=rkkrec[ToCrystalPath[SYT],n];

(*Convert a rigged configuration back to a standard Young tableau (SYT)*)
ToSYT[rigged_]:=ToTableau[kkrrec[ConstantArray[{1,1},Length[rigged[[1,1]]]],rigged[[2;;3]]]];



(* ::Subsection::Closed:: *)
(*Mode number to rigged configurations*)


Cartan[a_]:=SparseArray[{Band[{1,1}]->2,Band[{2,1}]->-1,Band[{1,2}]->-1},{a,a}]
Kernel[s_]:=Array[Min[#1,#2]&,{s,s}]

(*Code taking a Young diagram and producing all admissible string length collections and the bounds on the mode numbers for these.*)
TransposeYoungD[shape_] := 
 Table[Length[Select[shape, # > i &]], {i, 0, 
   shape[[1]] - 1}](*Populating the Transpose diagram; using Volin's code*)

MAS[a_, s_, shape_] := 
 Total[shape] - Sum[shape[[b]], {b, 1, a}] - 
  Sum[TransposeYoungD[shape][[t]], {t, 1, s}] + a*s 
(*Function M_as used in article*)

AugmentedYoungD[shape_] := 
 Block[{FilledYoungD, augmented},
   augmented = 
   Prepend[shape, shape[[1]]] + 
    1(*Creating a set of right size for finding all MAS values*);
  FilledYoungD = 
   Table[MAS[i - 1, j - 1,shape], {i, 
     Length[augmented]}, {j, augmented[[i]]}];
; FilledYoungD] (*Filling the Young diagram with M_as values*)

Msetmatrix[yd_]:=Module[{Ms,Mmatrices,UpdMmatrices,M},
Ms=Delete[First/@AugmentedYoungD[yd],{{1},{-1}}];
Mmatrices=PadRight/@(Map[Replace[{x__,0..}->{x}],Table[Solve[Sum[s*M[s],{s,1,\[Lambda]}]==\[Lambda],Table[M[t],{t,1,\[Lambda]}],NonNegativeIntegers],{\[Lambda],Ms}]//Values ,{2}]//Tuples)(*All possible Ms sets;the index is the string length and the value is the number of strings of that length*);
Table[Module[{},UpdMmatrices=matrix ;
Append[

Prepend[UpdMmatrices,SparseArray[1->(AugmentedYoungD[yd]//First//First),Length[UpdMmatrices[[1]]]]],ConstantArray[0,Length[UpdMmatrices[[1]]]]]]

,{matrix,Mmatrices}]
]

(*AdmissibleModes[yd_] return Admissible modenumber and Msetmatrix with first and last line removed and set zero to emtyp set*)
AdmissibleModes[yd_]:=Module[{Mmatrices},
Mmatrices=Msetmatrix[yd];
Table[
Module[{Holes,M\[LetterSpace]removeFirstLastZero,Holes\[LetterSpace]removeFirstLastZero},

Holes=-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[Length[Mmatrix[[1]]]];

Holes\[LetterSpace]removeFirstLastZero=Delete[-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[Length[Mmatrix[[1]]]],{{1},{-1}}];
M\[LetterSpace]removeFirstLastZero=Delete[Mmatrix/.{0->{}},{{1},{-1}}];

If[AllTrue[Holes\[LetterSpace]removeFirstLastZero//Flatten,GreaterEqualThan[0]],
{(Holes\[LetterSpace]removeFirstLastZero+M\[LetterSpace]removeFirstLastZero)/2-1/2,M\[LetterSpace]removeFirstLastZero}
,Nothing]

],

{Mmatrix,Mmatrices}]//Transpose]


(*Code finding all rigged configurations for a given Young diagramme*)
ModesConfig[yd_]:=Module[{},
Modes=AdmissibleModes[yd][[1]];
Mmatrices=AdmissibleModes[yd][[2]];
Table[
Tuples[Table[Tuples[Table[Subsets[Range[-Modes[[i]][[j]][[k]],Modes[[i]][[j]][[k]]],{Mmatrices[[i]][[j]][[k]]//Total}],{k,Length[Modes[[i]][[j]]]}]],{j,Length[Modes[[i]]]}]],{i,Length[Modes]}]//Catenate]


ModestoRiggedConfig[L_,modes_]:=Module[{Mmatrix,limits,deleteFirstLastLine},
Mmatrix=PadRight[Append[Prepend[Table[Length[modes[[i,j]]],{i,Length[modes]},{j,Length[modes[[i]]]}],SparseArray[1->L,1]],{0}]];

deleteFirstLastLine[x_]:=Delete[x,{{1},{-1}}];
limits=1/2 deleteFirstLastLine[-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[Length[Mmatrix[[1]]]]+Mmatrix/.{0->{}}]-1/2;

Prepend[

Append[{}]/@(Table[{Table[ConstantArray[i,Length[modes[[j,i]]]],{i,Sort[Range[Length[modes[[j]]]],Greater]}]//Catenate,Table[limits[[j,i]]+modes[[j,i,k]]+1-k,{i,Sort[Range[Length[modes[[j]]]],Greater]},{k,Length[modes[[j,i]]]}]//Catenate},{j,Length[modes]}]//Transpose)


,{ConstantArray[1,L]}]

]


(* ::Subsection:: *)
(*SolutionFromSYT*)


(* ::Code::Initialization:: *)
SolutionFromSYT[SYT_]:=Block[{},
\[Lambda]T=SYT;
\[Lambda]=SYT//ToYD;
GenerateQsystem[\[Lambda]];
Large\[CapitalLambda]Expansion;
SubleadingOrders;
GenerateEqnsForNumerics;
SolveAt\[CapitalLambda]0;
GenerateSolsFromAsymptotics;
\[CapitalLambda]vals=\[CapitalLambda]vals0;
(* the previous line resets \[CapitalLambda]vals - a record for which \[CapitalLambda] solution was already found *)
Iterateit;
];


(* ::Subsection::Closed:: *)
(*StepIterate*)


(* ::Code::Initialization:: *)
OldStepIterate[]:=Block[{},
(* Iteration procedure *)
Iterateit:=Block[{},
pp=pmin;qq=1;
step:=qq/base^pp;
(* starting the procedure *)
\[CapitalLambda]Last=\[CapitalLambda]vals[[-1]];
Monitor[
While[\[CapitalLambda]Last>\[CapitalLambda]target,If[step<10^-10,Throw["step goes to zero"]];
\[CapitalLambda]new=Max[\[CapitalLambda]Last-step,\[CapitalLambda]target];
normedrel=InterpEqns[\[CapitalLambda]new];
Which[
Catch[SilentFindSolit]==="Too big step",
pp=pp+1,
i>5,
sol[\[CapitalLambda]new]=minsolrep;
AppendTo[\[CapitalLambda]vals,\[CapitalLambda]new]
,
True,
sol[\[CapitalLambda]new]=minsolrep;
AppendTo[\[CapitalLambda]vals,\[CapitalLambda]new];
If[pp>pmin,qq=qq+\[CapitalDelta]q;If[qq==base,qq=1;pp=pp-1]];
];
\[CapitalLambda]Last=\[CapitalLambda]vals[[-1]]
],
Row@{"Current \[CapitalLambda] history is: ",\[CapitalLambda]vals//N,"current \[CapitalLambda] is: ",\[CapitalLambda]Last//N, "   step is: ",step//N}];
];
]

(*0.5 and 7 is good*)
NewStepIterate[howcloselambda1_,smalllambda_]:=Block[{},
Iterateit:=Block[{},
pp=pmin;qq=1;
step:=Module[{baseStep},baseStep=qq/base^pp;
If[\[CapitalLambda]Last-\[CapitalLambda]target<=howcloselambda1,baseStep/smalllambda,(*reduce step if very close to the target*)baseStep]];
(* starting the procedure *)
\[CapitalLambda]Last=\[CapitalLambda]vals[[-1]];
Monitor[
While[\[CapitalLambda]Last>\[CapitalLambda]target,If[step<10^-10,Throw["step goes to zero"]];
\[CapitalLambda]new=Max[\[CapitalLambda]Last-step,\[CapitalLambda]target];
normedrel=InterpEqns[\[CapitalLambda]new];
Which[
Catch[SilentFindSolit]==="Too big step",
pp=pp+1,
i>5,
sol[\[CapitalLambda]new]=minsolrep;
AppendTo[\[CapitalLambda]vals,\[CapitalLambda]new]
,
True,
sol[\[CapitalLambda]new]=minsolrep;
AppendTo[\[CapitalLambda]vals,\[CapitalLambda]new];
If[pp>pmin,qq=qq+\[CapitalDelta]q;If[qq==base,qq=1;pp=pp-1]];
];
\[CapitalLambda]Last=\[CapitalLambda]vals[[-1]]
],
Row@{"Current \[CapitalLambda] history is: ",\[CapitalLambda]vals//N,"current \[CapitalLambda] is: ",\[CapitalLambda]Last//N, "   step is: ",step//N}];
]
]


(* ::Subsection::Closed:: *)
(*Qdistance*)


(* ::Code::Initialization:: *)
Qdistance[sol1_,sol2_,indexSol_]:=Module[{commonElements,firstColumn1,firstColumn2,filteredFirstColumn1,filteredFirstColumn2},
commonElements=Intersection[sol1[[3]],sol2[[3]]];

firstColumn1=Transpose[{sol1[[3]],sol1[[2]]}];
firstColumn2=Transpose[{sol2[[3]],sol2[[2]]}];

filteredFirstColumn1=Select[firstColumn1,MemberQ[commonElements,#[[1]]]&][[All,2,indexSol]];filteredFirstColumn2=Select[firstColumn2,MemberQ[commonElements,#[[1]]]&][[All,2,indexSol]];

Transpose[{Reverse[commonElements],Map[Total[#]&,Abs[filteredFirstColumn1[[All,2]]-filteredFirstColumn2[[All,2]]]^2]}]


]


Qintdistance[sol1_,sol2_,indexSol_]:=Module[{commonElements,firstColumn1,firstColumn2,filteredFirstColumn1,filteredFirstColumn2},
commonElements=Intersection[sol1[[3]],sol2[[3]]];

firstColumn1=Transpose[{sol1[[3]],sol1[[4]]}];
firstColumn2=Transpose[{sol2[[3]],sol2[[4]]}];

filteredFirstColumn1=Select[firstColumn1,MemberQ[commonElements,#[[1]]]&][[All,2,indexSol]];filteredFirstColumn2=Select[firstColumn2,MemberQ[commonElements,#[[1]]]&][[All,2,indexSol]];

Transpose[{Reverse[commonElements],Map[Total[#]&,NIntegrate[Abs[filteredFirstColumn1[[All,2]]-filteredFirstColumn2[[All,2]]]^2,{u,-20,20}]^(1/2)
]

}]

]


(* ::Subsection::Closed:: *)
(*FindDuplicateRootPositions*)


(* ::Code::Initialization:: *)
FindDuplicateRootPositions[solvedBetheroots_]:=Module[{roundedBetheRoots
,tallyBetheRoots,rootMultiplicity,duplicatePositions,duplicateRoots,duplicateRootPositions,duplicateRootPositionsFlatten},
roundedBetheRoots = Round[solvedBetheroots[[All, 1]], 10^-5]; (* Round Bethe roots to 5 decimal places *)
tallyBetheRoots = Tally[roundedBetheRoots]; (* Count occurrences of each rounded root *)
rootMultiplicity = tallyBetheRoots[[All, 2]]; (* Extract multiplicities *)
duplicatePositions = 
  Flatten[Position[rootMultiplicity, x_ /; x != 1]]; (* Identify positions where multiplicity \[NotEqual] 1 *)
duplicateRoots = Table[tallyBetheRoots[[All, 1]][[k]], {k, duplicatePositions}]; (* Extract duplicate roots *)
duplicateRootPositions = Table[
   Position[roundedBetheRoots, duplicateRoots[[k]]], 
   {k, Length[duplicateRoots]}
] ;(* Find positions of duplicate roots in original list *)
duplicateRootPositionsFlatten=Flatten[#,1]&/@duplicateRootPositions

]


(* ::Subsection::Closed:: *)
(*newlazysolver*)


(* ::Code::Initialization:: *)
lazySolver[yd_, riggs_, maxTime_ : 40, maxRetries_ : 10] := 
  Module[{L, rigs, mySYT, attempt, result, paramValue},
    
     paramValue = 40; (* Initial value of parameter *)
    L = Total[yd];
    rigs = ModestoRiggedConfig[L, #] & /@ ModesConfig[yd];
    mySYT = ToSYT /@ rigs;
    
    Print["Running rigged configuration: ", riggs];
    
    (* Retry loop with increasing parameter values *)
    attempt = 0;
    result = False; (* Initialize result to failed state *)
    
    While[attempt < maxRetries && result === False,
      
      Print["Current paramValue: ", paramValue];
      
      parameter[paramValue]; (* Set parameter value *)
      attempt++;
      
      result = If[Catch[SolutionFromSYT[mySYT[[riggs]]]]==="step goes to zero",False,True];
                NotebookDelete[Cells[CellStyle -> "Print"]];
      (* If the result is successful, exit loop *)
      If[result =!= False, Break[],paramValue += 20];
      
      (* Increase parameter only when SolutionFromSYT fails *)
      
    ];
    
    (* If all attempts failed, return None and riggs *)
    If[result === False, Return[{None, riggs}],
     
     (* Proceed only if SolutionFromSYT succeeded *)
     
   
     
     Module[{allbetheQ, mysol, allbetherootEqns, solvedBetheroots, 
       listCcoefficient, listUmonomial, listUmonomialValue, 
       listUmonomialCoffValue},
       Print["succeeded with prec: " ,paramValue];
       allbetheQ = {};
       mysol = 
         Table[YQa[a, 0], {a, Length[\[Lambda] - 1]}] /. 
           First[vars2nvars /. {FindSolit[[2]]} /. \[CapitalLambda] -> 1];
       
       AppendTo[allbetheQ, mysol];
       
       allbetherootEqns = Map[# == 0 &, allbetheQ, {2}][[All, 1 ;; 2]];
       solvedBetheroots =
         (Table[
                 Table[
                   Solve[allbetherootEqns[[w]][[k]], u],
                   {k, Length[allbetherootEqns[[w]]]}],
                 {w, Length[allbetherootEqns]}] // Values) - 1;
       
       listCcoefficient = 
         Table[vars2nvars /. \[CapitalLambda] -> \[CapitalLambda]vals[[
          k]] /. 
             sol[\[CapitalLambda]vals[[k]]], {k, 
             Length[\[CapitalLambda]vals]}];
       
       listUmonomial = 
         Table[{k, \[CapitalLambda]vals[[k]], 
             Table[YQa[a, 0], {a, Length[\[Lambda]] - 1}]}, {k, 
             Length[\[CapitalLambda]vals]}];
       
       listUmonomialValue = 
         MapThread[
           ReplaceAll, {listUmonomial[[All, 3]], listCcoefficient}];
       
       listUmonomialCoffValue = CoefficientList[listUmonomialValue, u];
       
       {solvedBetheroots, listUmonomialCoffValue, \[CapitalLambda]vals,listUmonomialValue}
       ]
   ]]



(* ::Code::Initialization:: *)
newlazysolver[yd_] := Module[{solvedBetheroots, duplicateRootPositions, 
   previousDuplicateRootPositions, iterationstep, newsolutions, changedPositions},

  OldStepIterate[];
  solvedBetheroots = ParallelTable[lazySolver[yd, rigg,50,4], {rigg, Length[rigs]}];
  NotebookDelete[Cells[CellStyle -> "Print"]]; (* Clear previous print outputs *)

  
  duplicateRootPositions = FindDuplicateRootPositions[solvedBetheroots]//Flatten;
 Print["Original duplicate positions: " ,FindDuplicateRootPositions[solvedBetheroots]];
 previousDuplicateRootPositions = {}; (* Start with an empty comparison list *)

 
  iterationstep = 5;

  (* Iterate until there are no duplicate root positions *)
  While[Length[duplicateRootPositions]!=0,
   
    (* Find positions that changed from the last iteration *)
    (*changedPositions = Complement[duplicateRootPositions, previousDuplicateRootPositions];*)

    (* Update only if any positions have changed *)
    If[Length[duplicateRootPositions]!=0,

      (* Perform iteration step with increasing parameter *)
      NewStepIterate[0.3, iterationstep];
      iterationstep++; (* Increment iteration step *)

      (* Solve again only for the changed duplicate positions *)
      newsolutions = ParallelTable[
          lazySolver[yd, duplicateRootPositions[[position]],50,4],
          {position, Length[duplicateRootPositions]}];

NotebookDelete[Cells[CellStyle -> "Print"]];
      (* Update solvedBetheroots only for changed positions *)
      Do[
        solvedBetheroots[[duplicateRootPositions[[position]]]] = newsolutions[[ position]],
        {position, Length[duplicateRootPositions]}
      ];
,
    (* Update previous duplicate positions before next iteration *)
    previousDuplicateRootPositions = duplicateRootPositions;

    ];



    (* Update duplicate root positions based on the modified solvedBetheroots *)
    duplicateRootPositions = FindDuplicateRootPositions[solvedBetheroots]//Flatten;
 Print["step: ",iterationstep-1," Next duplicate positions: " ,FindDuplicateRootPositions[solvedBetheroots]];
  ];

  (* Return the updated set of solved roots *)
  solvedBetheroots
]


(* ::Subsection:: *)
(*Test*)


(* ::Input:: *)
(*yd={4,1};*)
(*L=Total[yd];*)
(*rigs=ModestoRiggedConfig[L,#]&/@ModesConfig[yd];*)
(*showRC/@rigs;*)
(*mySYT=ToSYT/@rigs;*)
(*iterativLazysolver=newlazysolver[yd];*)
(*(*SolutionFromSYT[mySYT[[1]]]*)*)



