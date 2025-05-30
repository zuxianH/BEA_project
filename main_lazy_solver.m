(* ::Package:: *)

(* ::Subsection::Closed:: *)
(*Parameter*)


(* ::Code::Initialization:: *)
maxord=5; (* Number of orders in analytic 1/\[CapitalLambda] expansion of large \[Theta] solution. Generation of each next order is time-costly.  Roughly, the lower maxord is the bigger \[CapitalLambda]0 is needed *)
\[CapitalLambda]0=4; (* use analytic expressions as a solution guess for \[CapitalLambda]\[GreaterEqual]\[CapitalLambda]0. Large \[CapitalLambda] may need larger prec. May need \[CapitalLambda]0=4 for big systems *)
prec=40; (* Precision to use in computations. If iteration step drops below 10^-6, try increasing precision. Until length 16 prec=40 should be ok, then need prec=80 sometimes. After length 20, need play more seriously with prec *)
interpord=25; (* how many points from previous computations to take to guess the next step. Seriously affects convergence speed. Good values are between approx. 20 and 40 and depend on solution. *)
startinterpord=10; (* how many points to generate from asymptotic solution *)
$MaxPrecision=Infinity;(* I don't remember why I neded this. Maybe already irrelevant *)
MyMaxIterations=12; (* Number of iterations before aborting attempts to converge. *) 
base=2;pmin=3;RecoverySpeed=1/7;
\[CapitalDelta]q=(base-1)Min[1,RecoverySpeed];(* step of iteration is computed as q/base^p and it is automatically adjusted: q\[Rule]q+\[CapitalDelta]q if converges fast; p\[Rule]p+1 if computation aborts; q\[Rule]1,p\[Rule]p-1 if q=base *)
(* increase base and/or pmin if you want to reduce maximal allowed step *)
\[CapitalLambda]target=1; (* when to terminate iteration *)


(* ::Subsection::Closed:: *)
(*Standard commands*)


(* ::Code::Initialization:: *)
(* Compute the multiplicity of a partition \[Lambda] *)
mult[\[Lambda]_] := Plus @@ \[Lambda]! / 
  Product[
    (\[Lambda][[Length[\[Lambda]] - a]] + a)! / 
      Product[
        \[Lambda][[Length[\[Lambda]] - a]] - 
        \[Lambda][[Length[\[Lambda]] - k]] + (a - k), 
        {k, 0, a - 1}
      ], 
    {a, 0, Length[\[Lambda]] - 1}
  ];

(* Compute the dual diagram (conjugate partition) of a Young diagram *)
DualDiagram[\[Lambda]_] := Total /@ Transpose[
  (PadRight[#1, \[Lambda][[1]]] &) /@ 
  (ConstantArray[1, #1] &) /@ \[Lambda]
];

(* Convert a standard Young tableau (SYT) to its Young diagram shape *)
ToYD[stb_] := Length /@ stb;

(* Check if a tableau \[Lambda]T is a valid standard Young tableau (SYT) *)
CheckStandard[\[Lambda]T_] := 
  And @@ Flatten[
    {
      (* Check row-wise increasing order *)
      Table[
        \[Lambda]T[[a - 1, s]] < \[Lambda]T[[a, s]], 
        {a, 2, Length[\[Lambda]T]}, 
        {s, 1, Length[\[Lambda]T[[a]]]}
      ],
      
      (* Check column-wise increasing order *)
      Table[
        \[Lambda]T[[a, s - 1]] < \[Lambda]T[[a, s]], 
        {a, 1, Length[\[Lambda]T]}, 
        {s, 2, Length[\[Lambda]T[[a]]]}
      ],
      
      (* Ensure the tableau contains numbers 1 to n without repetition *)
      Sort[Flatten[\[Lambda]T]] == Range[Length[Flatten[\[Lambda]T]]],
      
      (* Ensure the structure is a list of lists *)
      ListQ /@ \[Lambda]T
    }
  ];



(* ::Code::Initialization:: *)
(* Compute the Wronskian determinant of two functions A and B *)
Wronsk[A_, B_] := (A /. u -> u + I/2) * (B /. u -> u - I/2) - 
                   (A /. u -> u - I/2) * (B /. u -> u + I/2);

(* Normalize a polynomial A to make it monic (leading coefficient = 1) *)
toMonic[A_] := Collect[
  ( # / Coefficient[#, u, Exponent[#, u]] & )[
    Expand[A]
  ], 
  u
];



(* ::Code::Initialization:: *)
mPrint[x___]:=Print[x];
PrintDone[x_]:=mPrint["...Done in: ",Timing[x][[1]],"s"];
SetAttributes[PrintDone,HoldAll];


(* ::Subsection::Closed:: *)
(*GenerateQsystem*)


(* ::Text:: *)
(*GenerateQsystem generates all QQ-relations. Input is  \[Lambda] - a Young diagram, you can also tinker with the code and specify Domain of interest (collection of {a,s} specifying which QQ-relations to take into account). The other code is compatible with this specification. *)


(* ::Code::Initialization:: *)
(* Generate QQ system relations for a given Young diagram \[Lambda] *)
GenerateQsystem[\[Lambda]_] := Block[{},
  
  mPrint["Generating QQ relations on Young diagram..."];
  
  (* Length of the spin chain *)
  Len = Total[\[Lambda]];
  
  (* Unprotect and clear M due to conflict with Combinatorica package *)
  Unprotect[M]; ClearAll[M];

  (* Define the full domain of interest (FullYoungDiagram) *)
  FullYoungDiagram = Block[{mm}, 
    Flatten@Table[mm[a, s], {a, 0, Length[\[Lambda]] - 1}, {s, 0, \[Lambda][[a + 1]] - 1}] /. mm -> List
  ];
  
  DomainOfInterest = FullYoungDiagram;

  (* Uncomment the block below to define a non-standard DomainOfInterest *)
  (* 
  DomainOfInterest = Block[{mm}, 
    Flatten@Table[mm[a, s], {a, 0, 1}, {s, 0, 1}] /. mm -> List
  ]; 
  *)

  (* Define function M[a, s] that computes specific entries *)
  M[a_, s_] := M[a, s] = Len + a s - Total[\[Lambda][[1 ;; a]]] - Total[DualDiagram[\[Lambda]][[1 ;; s]]];

  (* Define Y-functions *)
  YQa[0, 0] := u^Len + Sum[u^(Len - k) sym[k], {k, Len}];
  YQa[a_, s_] := u^M[a, s] + Sum[c[a, s, k] u^(M[a, s] - k), {k, M[a, s]}];
  
  (* Define transformed YQ functions *)
  YQ\[Theta][0, 0] = YQa[0, 0];
  YQ\[Theta][a_, s_] := Product[u - q\[Theta][a, s, k], {k, 1, M[a, s]}];

  (* QQ relation *)
  QQrel[a_, s_] := CoefficientList[
    (YQa[a, s] /. u -> u + I/2) * (YQa[a + 1, s + 1] /. u -> u - I/2) -
    (YQa[a, s] /. u -> u - I/2) * (YQa[a + 1, s + 1] /. u -> u + I/2) -
    I (M[a, s] - M[a + 1, s + 1]) YQa[a + 1, s] YQa[a, s + 1], 
    u
  ] // (# /. Complex[0, b_] :> b) &;

  (* Compute all QQ relations in the domain of interest *)
  Allrel = Monitor[
    Table[
      If[MemberQ[DomainOfInterest, {a, s}] && M[a, s] > 0, QQrel[a, s], Nothing], 
      {a, 0, Length[\[Lambda]] - 1}, 
      {s, 0, \[Lambda][[a + 1]] - 1}
    ],
    {a, s}
  ] // Flatten;

  (* Variables: coefficients of all Q-functions *)
  vars = Table[
    If[a + s == 0, Nothing, c[a, s, k]], 
    {a, 0, Length[\[Lambda]] - 1}, 
    {s, 0, \[Lambda][[a + 1]] - 1}, 
    {k, M[a, s]}
  ] // Flatten;

  (* Select only those variables appearing in the domain of interest *)
  vars2 = DeleteCases[Variables[Allrel], sym[_]];

  (* Print summary of the computation *)
  mPrint@Column[{
    Row[{"Length of spin chain: ", Len}],
    Row[{"Number of SYT: ", mult[\[Lambda]]}],
    Row[{"Domain of Interest: ", 
      MatrixPlot[#, Mesh -> True] & @ Table[
        Which[
          MemberQ[DomainOfInterest, {a, s}], 1,
          MemberQ[FullYoungDiagram, {a, s}], 1/2,
          True, 0
        ], 
        {a, 0, Length[\[Lambda]] - 1}, 
        {s, 0, \[Lambda][[1]] - 1}
      ]
    }],
    Row[{"Number of variables: ", Length[vars2]}],
    Row[{"Number of equations: ", Length[Allrel]}]
  }];

] // PrintDone;



(* ::Subsection::Closed:: *)
(*showSYT*)


(* ::Text:: *)
(*showSYT will draw SYT with \[Lambda]T as global area. Shaded region is decided domain of interest*)


(* ::Code::Initialization:: *)
(* Function to visualize a standard Young tableau (SYT) *)
showSYT[\[Lambda]T_] := Graphics[
  Table[
    {
      (* Display the entry in the tableau *)
      Text[Style[\[Lambda]T[[a, s]], Small, Black], {s, -a}],
      
      (* Set transparency for better visualization *)
      Opacity[0.5], 
      
      (* Light gray background for boxes *)
      Lighter[Lighter[Gray]], 
      
      (* Draw the rectangle representing the tableau cell *)
      Rectangle[{s - 1/2, -a - 1/2}]
    }, 
    {a, 1, Length[\[Lambda]T]}, 
    {s, 1, Length[\[Lambda]T[[a]]]}
  ], 
  ImageSize -> Tiny
];

(* Function to visualize an SYT with the domain of interest (DOI) highlighted *)
showSYT[\[Lambda]T_, "DOI"] := Graphics[
  Table[
    {
      (* Display the entry in the tableau *)
      Text[Style[\[Lambda]T[[a, s]], Small, Black], {s, -a}],
      
      (* Set transparency for better visualization *)
      Opacity[0.5], 
      
      (* Light gray background for boxes *)
      Lighter[Lighter[Gray]], 
      
      (* Draw the rectangle representing the tableau cell *)
      Rectangle[{s - 1/2, -a - 1/2}],
      
      (* Highlight cells that belong to the domain of interest *)
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



(* ::Subsection::Closed:: *)
(*init\[Theta]rep*)


(* ::Text:: *)
(*Solution of Q-system in the large \[CapitalLambda] limit, the leading order*)


(* ::Code::Initialization:: *)
(* Function to initialize the \[Theta] representation for a given Young tableau \[Lambda]T *)
init\[Theta]rep[\[Lambda]T_] := init\[Theta]rep[\[Lambda]T] = Block[{kk, sd},
  
  (* Initialize the counter function kk *)
  kk[_, _] = 0;
  
  (* Define the selection function sd, which filters elements of \[Lambda]T *)
  sd[m_] := (Select[#1, #1 <= m &] &) /@ \[Lambda]T;

  (* Check if \[Lambda]T is a standard tableau before proceeding *)
  If[CheckStandard[\[Lambda]T],

    (* Generate sorted and flattened list of transformations *)
    Sort[Flatten[
      Table[
        Table[
          If[
            (* The condition `True || MemberQ[...]` is always True; MemberQ is redundant *)
            True || MemberQ[DomainOfInterest, {a2, s2}],
            
            (* Define q\[Theta] transformation rule *)
            q\[Theta][a2, s2, ++kk[a2, s2]] -> 
              Product[
                (Length[sd[\[Lambda]T[[a, s]]][[a3]]] + a - s - a3) / 
                (Length[sd[\[Lambda]T[[a, s]]][[a3]]] + a - s - a3 + 1), 
                {a3, 1, a2}
              ] *
              Product[
                (DualDiagram[Length /@ sd[\[Lambda]T[[a, s]]]][[s3]] + s - a - s3) / 
                (DualDiagram[Length /@ sd[\[Lambda]T[[a, s]]]][[s3]] + s - a - s3 + 1), 
                {s3, 1, s2}
              ] *
              \[Theta][\[Lambda]T[[a, s]]],
            
            (* If condition fails, return Nothing *)
            Nothing
          ],
          {a2, 0, a - 1}, {s2, 0, s - 1}
        ],
        {a, 1, Length[\[Lambda]T]}, {s, 1, Length[\[Lambda]T[[a]]]}
      ]
    ]],

    (* If not a standard tableau, print a warning message *)
    Print["Not standard tableau"]
  ]
];



(* ::Subsection::Closed:: *)
(*Large\[CapitalLambda]Expansion*)


(* ::Text:: *)
(*Generating system of relations with leading coefficient plugged in. Working only up to maxord (I think I overdo one order)*)


(* ::Code::Initialization:: *)
(* Perform 1/\[CapitalLambda] expansion of QQ system around the chosen SYT solution *)
Large\[CapitalLambda]Expansion := Block[{},
  
  mPrint["1/\[CapitalLambda] expansion of QQ system around the chosen SYT solution..."];
  
  (* Display the chosen SYT solution *)
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



(* ::Subsection::Closed:: *)
(*SubleadingOrders*)


(* ::Text:: *)
(*Generating list of subleading equations and solving them.*)


(* ::Code::Initialization:: *)
(* Solve subleading orders in the 1/\[CapitalLambda] expansion *)
SubleadingOrders := Block[{},
  
  mPrint["Arranging and solving 1/\[CapitalLambda] analytic equations for c..."];

  (* Compute the series expansion for each equation in 'anlytic' *)
  sublead = Monitor[
    Table[
      Normal @ Series[
        (# / \[CapitalLambda]^Exponent[#, \[CapitalLambda]]) &[anlytic[[k]]], 
        {\[CapitalLambda], \[Infinity], maxord}
      ],
      {k, Length[anlytic]}
    ],
    k
  ];

  (* Define a cutoff term to restrict orders of \[CapitalLambda] *)
  cutoff = Series[\[CapitalLambda], {\[CapitalLambda], \[Infinity], maxord - 1}] - \[CapitalLambda];

  (* Generate subleading equations by replacing ecc terms with their expansions *)
  subleadingeqns = Monitor[
    Table[
      (sublead[[k]] /. ecc[a_, s_, k_] :> 
        Sum[ecc[ord][a, s, k] / \[CapitalLambda]^(ord - 1), {ord, 1, maxord}] + cutoff
      )[[3]],
      {k, Length[sublead]}
    ],
    k
  ];

  (* Solve the subleading equations order by order *)
  Do[
    \[CapitalLambda]sol[ord] = Solve[
      subleadingeqns[[All, ord]] == 0 /. Flatten@Table[\[CapitalLambda]sol[k], {k, ord - 1}], 
      vars2 /. c[a_, s_, k_] :> ecc[ord][a, s, k]
    ][[1]],
    {ord, maxord}
  ];

] // PrintDone;



(* ::Input:: *)
(*GenerateQsystem[{4,2,1}]*)
(*\[Lambda]T={{1,3,6,7},{2,5},{4}}*)
(*showSYT[{{1,3,6,7},{2,5},{4}}]*)
(*init\[Theta]rep[\[Lambda]T]*)
(*Large\[CapitalLambda]Expansion*)
(*symrep*)
(*SubleadingOrders*)


(* ::Subsection::Closed:: *)
(*GenerateEqnsForNumerics*)


(* ::Code::Initialization:: *)
(* Generate equations for numerical iterations *)
GenerateEqnsForNumerics := Block[{},
  
  mPrint["Generating equations for numerical iterations"];
  
  (* Normalized variables and equations, max powers of \[CapitalLambda] are taken out *)

  (* Define normalized variables by replacing c[a,s,k] with nc[a,s,k] *)
  nvars = vars2 /. c -> nc;
  
  (* Define transformation rules between sym and nsym variables *)
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
      vars2 /. c[a_, s_, k_] :> (\[CapitalLambda]^-Exponent[c[a, s, k] /. ftransit, \[CapitalLambda]] c[a, s, k])
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



(* ::Subsection::Closed:: *)
(*AsymEqns*)


(* Generating equations using asymptotic approximation *)
AsymEqns[\[CapitalLambda]0_] := Block[{},
  (* Substitute \[CapitalLambda] with \[CapitalLambda]0 in nsymrep and ntransit *)
  nsymrep = nfsymrep /. \[CapitalLambda] -> \[CapitalLambda]0;
  ntransit = nftransit /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Create substitution rules for nc expressions with asymptotic corrections *)
  subnc = Thread[
    Rule[
      nvars,
      nvars /. (nc[a_, s_, k_] :> 
         (1 + 1/\[CapitalLambda]0 Sum[
             1/\[CapitalLambda]0^(ord - 1) (ecc[ord][a, s, k] /. \[CapitalLambda]sol[ord]),
             {ord, 1, maxord}
           ]) nc[a, s, k]) /. ntransit
    ]
  ];
  
  (* Apply the substitution to the normalized equations and simplify *)
  #/(1 + Abs[# /. nc[a_, s_, k_] :> (nc[a, s, k] /. subnc)]) & /@
    (NormedEqns /. nsymrep /. \[CapitalLambda] -> \[CapitalLambda]0)
    // Expand
];

(* Generating equations using previous order results and polynomial fit *)
InterpEqns[\[CapitalLambda]0_] := Block[
  {minterpord = Min[Length[\[CapitalLambda]vals] - 1, interpord]},
  
  (* Substitute \[CapitalLambda] with \[CapitalLambda]0 in nsymrep *)
  nsymrep = nfsymrep /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Create substitution rules for nc expressions using interpolation 
     with previous order results *)
  subnc = Thread[
    Rule[
      nvars,
      Round[
        Sum[
          (nvars /. sol[\[CapitalLambda]vals[[-j]]]) *
            Product[
              If[j == j2, 
                1, 
                (\[CapitalLambda]0 - \[CapitalLambda]vals[[-j2]])/(\[CapitalLambda]vals[[-j]] - \[CapitalLambda]vals[[-j2]])
              ],
              {j2, minterpord}
            ],
          {j, minterpord}
        ],
        10^-prec
      ]
    ]
  ];
  
  (* Apply the interpolation substitution to the normalized equations and simplify *)
  #/(# /. nc[a_, s_, k_] :> ((1 + Round[Random[]/100, 10^-5]) nc[a, s, k] /. subnc)) & /@
    (NormedEqns /. nsymrep /. \[CapitalLambda] -> \[CapitalLambda]0)
    // Expand
];

(* Routine to produce a solution with monitoring of the minimization process *)
FindSol := (
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
    Row@{"Step: ", i, ",   Minim: ", norm}
  ]
);

(* Routine to produce a solution silently (without monitoring) *)
SilentFindSol := (
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



(* ::Subsection::Closed:: *)
(*SolveAt\[CapitalLambda]0*)


(* ::Code::Initialization:: *)
(* Solving first point solution, to decide where to start *)
SolveAt\[CapitalLambda]0 := Block[{},
  
  (* Inform the user about the current attempt at \[CapitalLambda]0 *)
  mPrint["Checking if can solve at \[CapitalLambda]0. If this produces mistakes, increase \[CapitalLambda]0"];
  
  (* Initialize iteration counter *)
  i = 0;
  
  (* Generate the normalized equations at the given \[CapitalLambda]0 using asymptotic approximation *)
  normedrel = AsymEqns[\[CapitalLambda]0];
  
  (* Find the numerical solution for the current \[CapitalLambda]0 *)
  FindSol;
  
  (* Print the minimized value numerically *)
  minim // N // mPrint;
];



(* ::Subsection::Closed:: *)
(*GenerateSolsFromAsymptotics*)


(* ::Code::Initialization:: *)
(* Generating first sample points for interpolation 
   and for some large \[CapitalLambda] expressions *)
GenerateSolsFromAsymptotics := Block[{},
  
  mPrint["Initialise: Numerical solutions from analytic 1/\[CapitalLambda] approximation"];
  
  (* Initialize list to store the \[CapitalLambda] values obtained *)
  \[CapitalLambda]vals0 = {};
  
  (* Create a range of \[CapitalLambda] values for initial interpolation.
     The range is built starting at \[CapitalLambda]0 with a step of 1/40, 
     for (startinterpord - 1) steps. The result is flattened, unified, sorted, 
     and then reversed. *)
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;
  
  (* For each \[CapitalLambda] value in the range, compute a numerical solution *)
  Monitor[
    Do[
      (* Generate normalized equations using the asymptotic approximation at the current \[CapitalLambda] value *)
      normedrel = AsymEqns[\[CapitalLambda]0];
      
      (* Solve the system for the current \[CapitalLambda] value *)
      FindSol;
      
      (* Optionally, an alternative solution assignment is commented out *)
      (* sol[\[CapitalLambda]0] := Thread[Rule[vars2, (vars2/.subc)(vars3/.minsolrep)]]; *)
      
      (* Store the numerical solution obtained *)
      sol[\[CapitalLambda]0] = minsolrep;
      
      (* Append the current \[CapitalLambda] value to the list *)
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];
      
      , {\[CapitalLambda]0, rng}
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}]
  ] // PrintDone;
];



(* ::Subsection::Closed:: *)
(*Iterate*)


(* ::Code::Initialization:: *)
(* Iteration procedure for numerical solutions *)
Iterate := Block[{},
  
  (* Display initial messages *)
  mPrint["Numerical iterations towards \[CapitalLambda] = ", \[CapitalLambda]target];
  mPrint["If step becomes below \!\(\*SuperscriptBox[\(10\), \(-7\)]\), try to increase prec"];
  
  (* Initialize iteration parameters *)
  pp = pmin; 
  qq = 1;
  step := qq / base^pp;
  
  (* Start the iterative procedure *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
  
  (* Monitor the iterative process *)
  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,
      
      (* Compute the next \[CapitalLambda] value, ensuring it doesn't go below \[CapitalLambda]target *)
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
      
      (* Generate the interpolated equations for the new \[CapitalLambda] value *)
      normedrel = InterpEqns[\[CapitalLambda]new];
      
      (* Solve numerically and adjust step size if needed *)
      Which[
        
        (* If step is too big, increase precision scaling factor pp *)
        Catch[SilentFindSol] === "Too big step",
        pp = pp + 1,
        
        (* If sufficient iterations are completed, store solution and continue *)
        i > 5,
        sol[\[CapitalLambda]new] = minsolrep;
        AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new],
        
        (* Default case: store solution and dynamically adjust step size *)
        True,
        sol[\[CapitalLambda]new] = minsolrep;
        AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];
        
        (* Adjust step size if pp is greater than pmin *)
        If[pp > pmin,
          qq = qq + \[CapitalDelta]q;
          If[qq == base, qq = 1; pp = pp - 1];
        ]
      ];
      
      (* Update the last \[CapitalLambda] value in the iteration *)
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
      
    ],
    
    (* Display the current \[CapitalLambda] value and step size during iteration *)
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
  ] // PrintDone;
  
  (* Display final message listing all computed \[CapitalLambda] values *)
  mPrint["Finished iterations. List of all \[CapitalLambda] computed: ", \[CapitalLambda]vals // N];
];



(* ::Subsection::Closed:: *)
(*Inits*)


(* ::Code::Initialization:: *)
(* Loading rigged configurations package *)
SetDirectory[NotebookDirectory[]]
<<RC.m;
(* Path \[LeftRightArrow] Tableaux *)
ToCrystalPath[stb_]:=Block[{len=Length[stb//Flatten]},Table[{{Position[stb,k][[1,1]]}},{k,len}]];
ToTableau[path_]:=Block[{pr=path//Flatten,max},max=Max[pr];
Table[Position[pr,k]//Flatten,{k,max}]];
Quiet[Needs["Combinatorica`"]];
(* Generating rigged *)
ToRigged[SYT_,n_:5]:=rkkrec[ToCrystalPath[SYT],n];
(* generating SYT from rigged *)
ToSYT[rigged_]:=ToTableau[kkrrec[ConstantArray[{1,1},Length[rigged[[1,1]]]],rigged[[2;;3]]]];


(* ::Subsubsection:: *)
(*Inits*)


(* ::Code::Initialization:: *)
(* Compute a solution starting from a given standard Young tableau (SYT) *)
SolutionFromSYT[SYT_] := Block[{},
  
  (* Assign the input SYT to global variables *)
  \[Lambda]T = SYT;
  \[Lambda] = SYT // ToYD;  (* Convert SYT to Young diagram shape *)

  (* Generate the Q-system for the given Young diagram *)
  GenerateQsystem[\[Lambda]];

  (* Perform a 1/\[CapitalLambda] expansion *)
  Large\[CapitalLambda]Expansion;

  (* Compute subleading orders in the 1/\[CapitalLambda] expansion *)
  SubleadingOrders;

  (* Generate equations for numerical solving *)
  GenerateEqnsForNumerics;

  (* Solve for the initial \[CapitalLambda] value *)
  SolveAt\[CapitalLambda]0;

  (* Generate initial solutions using asymptotic approximation *)
  GenerateSolsFromAsymptotics;

  (* Reset \[CapitalLambda]vals: keeps track of solved \[CapitalLambda] values *)
  \[CapitalLambda]vals = \[CapitalLambda]vals0;  

  (* Perform iterative numerical refinement *)
  Iterate;
];

(* Placeholder function for mPrint to suppress unnecessary output *)
mPrint[x_] := Null;



(* ::Subsection::Closed:: *)
(*Relating to rigged configurations*)


(* ::Code::Initialization:: *)
(* Loading rigged configurations package *)
SetDirectory[NotebookDirectory[]]
<<RC.m;
(* Path \[LeftRightArrow] Tableaux *)
ToCrystalPath[stb_]:=Block[{len=Length[stb//Flatten]},Table[{{Position[stb,k][[1,1]]}},{k,len}]];
ToTableau[path_]:=Block[{pr=path//Flatten,max},max=Max[pr];
Table[Position[pr,k]//Flatten,{k,max}]];
Quiet[Needs["Combinatorica`"]];
(* Generating rigged *)
ToRigged[SYT_,n_:5]:=rkkrec[ToCrystalPath[SYT],n];
(* generating SYT from rigged *)
ToSYT[rigged_]:=ToTableau[kkrrec[ConstantArray[{1,1},Length[rigged[[1,1]]]],rigged[[2;;3]]]];


"/home/zuxian/Documents/BAE_Project"


(* ::Subsection::Closed:: *)
(*Mode number to rigged configurations*)


(* ::Code::Initialization:: *)
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


(* ::Section:: *)
(*Test*)


yd={4,2,1};
L=Total[yd];
rigs=ModestoRiggedConfig[L,#]&/@ModesConfig[yd];
showRC/@rigs;
mySYT=ToSYT/@rigs;


SolutionFromSYT[mySYT[[1]]]



