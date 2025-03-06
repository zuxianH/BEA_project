(* ::Package:: *)

ClearAll["Global`*"]


(* ::Section:: *)
(*Lazysolver*)


(* ::Subsection:: *)
(*Parameter*)


(*maxord=5; (* Number of orders in analytic 1/\[CapitalLambda] expansion of large \[Theta] solution. Generation of each next order is time-costly.  Roughly, the lower maxord is the bigger \[CapitalLambda]0 is needed *)
\[CapitalLambda]0=4; (* use analytic expressions as a solution guess for \[CapitalLambda]\[GreaterEqual]\[CapitalLambda]0. Large \[CapitalLambda] may need larger prec. May need \[CapitalLambda]0=4 for big systems *)
prec=40; (* Precision to use in computations. If iteration step drops below 10^-6, try increasing precision. Until length 16 prec=40 should be ok, then need prec=80 sometimes. After length 20, need play more seriously with prec *)
interpord=40; (* how many points from previous computations to take to guess the next step. Seriously affects convergence speed. Good values are between approx. 20 and 40 and depend on solution. *)
startinterpord=10; (* how many points to generate from asymptotic solution *)
$MaxPrecision=Infinity;(* I don't remember why I neded this. Maybe already irrelevant *)
MyMaxIterations=12; (* Number of iterations before aborting attempts to converge. *) 
base=2;pmin=3;RecoverySpeed=1/7;
\[CapitalDelta]q=(base-1)Min[1,RecoverySpeed];(* step of iteration is computed as q/base^p and it is automatically adjusted: q\[Rule]q+\[CapitalDelta]q if converges fast; p\[Rule]p+1 if computation aborts; q\[Rule]1,p\[Rule]p-1 if q=base *)
(* increase base and/or pmin if you want to reduce maximal allowed step *)
\[CapitalLambda]target=1; (* when to terminate iteration *)*)


(* ::Subsection:: *)
(*Standard commands*)


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



mPrint[x___]:=Print[x];
PrintDone[x_]:=mPrint["...Done in: ",Timing[x][[1]],"s"];
SetAttributes[PrintDone,HoldAll];


(* ::Subsection:: *)
(*GenerateQsystem*)


(* ::Text:: *)
(*GenerateQsystem generates all QQ-relations. Input is  \[Lambda] - a Young diagram, you can also tinker with the code and specify Domain of interest (collection of {a,s} specifying which QQ-relations to take into account). The other code is compatible with this specification. *)


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



(* ::Subsection:: *)
(*showSYT*)


(* ::Text:: *)
(*showSYT will draw SYT with \[Lambda]T as global area. Shaded region is decided domain of interest*)


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



(* ::Subsection:: *)
(*init\[Theta]rep*)


(* ::Text:: *)
(*Solution of Q-system in the large \[CapitalLambda] limit, the leading order*)


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



(* ::Subsection:: *)
(*Large\[CapitalLambda]Expansion*)


(* ::Text:: *)
(*Generating system of relations with leading coefficient plugged in. Working only up to maxord (I think I overdo one order)*)


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



(* ::Subsection:: *)
(*SubleadingOrders*)


(* ::Text:: *)
(*Generating list of subleading equations and solving them.*)


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


(* ::Subsection:: *)
(*GenerateEqnsForNumerics*)


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



(* ::Subsection:: *)
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



(* ::Input:: *)
(*FindSol*)


(* ::Input:: *)
(*Table[sol[\[CapitalLambda]vals[[k]]], {k, Length[\[CapitalLambda]vals]}][[-1]]*)


(* ::Subsection:: *)
(*SolveAt\[CapitalLambda]0*)


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



(* ::Subsection:: *)
(*GenerateSolsFromAsymptotics*)


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



(* ::Subsection:: *)
(*Iterate*)


stepList = {}; (* Store steps *)
Iterate := Block[{},
  mPrint["Numerical iterations towards \[CapitalLambda] = ", \[CapitalLambda]target];
  mPrint["If step becomes below 10^-7, try to increase prec"];

  (* Initialize iteration parameters *)
  pp = pmin;
  qq = 1;
  

  step := (qq / base^pp);

  (* Start the iterative procedure *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,
      
      (* Compute next \[CapitalLambda] value *)
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];

      (* Append current step to the list *)
      AppendTo[stepList, step];

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

        (* Adjust step size dynamically *)
        If[pp > pmin,
          qq = qq + \[CapitalDelta]q;
          If[qq == base, qq = 1; pp = pp - 1];
        ]
      ];

      (* Update last computed \[CapitalLambda] value *)
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

    ],
    (* Display the current \[CapitalLambda] value and step size during iteration *)
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
  ] // PrintDone;
  
  (* Display final message listing all computed \[CapitalLambda] values *)
  mPrint["Finished iterations. List of all \[CapitalLambda] computed: ", \[CapitalLambda]vals // N];

];



Print[Iterate];
Iterate===Null


Iterate := Block[{},
  (* Initial messages *)
  mPrint["Numerical iterations towards \[CapitalLambda] = ", \[CapitalLambda]target];
  mPrint["If step becomes below 10^-7, try to increase prec"];

  (* Initialize iteration parameters *)
  pp = pmin;
  qq = 1;

  step := (qq / base^pp);

  (* Start the iterative procedure *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,

      (* Compute next \[CapitalLambda] value *)
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
      
      (* Append current step to the list *)
      AppendTo[stepList, step];

      (* If step is too small, print the message and exit *)
      If[step < 10^-7, Print["Too small step size"]; Return["bad"]];

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

        (* Adjust step size dynamically *)
        If[pp > pmin,
          qq = qq + \[CapitalDelta]q;
          If[qq == base, qq = 1; pp = pp - 1];
        ]
      ];

      (* Update last computed \[CapitalLambda] value *)
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

    ],
    (* Display the current \[CapitalLambda] value and step size during iteration *)
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
  ] // PrintDone;
  
  (* Display final message listing all computed \[CapitalLambda] values *)
  mPrint["Finished iterations. List of all \[CapitalLambda] computed: ", \[CapitalLambda]vals // N];
];



Iterate := Block[{},
  (* Initial messages *)
  mPrint["Numerical iterations towards \[CapitalLambda] = ", \[CapitalLambda]target];
  mPrint["If step becomes below 10^-7, try to increase prec"];

  (* Initialize iteration parameters *)
  pp = pmin;
  qq = 1;

  step := (qq / base^pp);

  (* Start the iterative procedure *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,

      (* Compute next \[CapitalLambda] value *)
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];

      (* If step is too small, print the message and return "TooSmallStepSize" *)
      If[step < 10^-7, Print["Too small step size"]; Return["TooSmallStepSize", Block]];

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

        (* Adjust step size dynamically *)
        If[pp > pmin,
          qq = qq + \[CapitalDelta]q;
          If[qq == base, qq = 1; pp = pp - 1];
        ]
      ];

      (* Update last computed \[CapitalLambda] value *)
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

    ],
    (* Display the current \[CapitalLambda] value and step size during iteration *)
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
  ] // PrintDone;
  
  (* Display final message listing all computed \[CapitalLambda] values *)
  mPrint["Finished iterations. List of all \[CapitalLambda] computed: ", \[CapitalLambda]vals // N];

  (* If iteration completes successfully, return Null *)
  Null
];




(* ::Subsection:: *)
(*Inits*)


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
(*SolutionFromSYT*)


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





SolutionFromSYT[SYT_] := Block[{
    stepThreshold = 10^-7,
    precIncrement = 10,
    maxPrec = 200, (* Maximum precision limit to avoid infinite loops *)
    solutionSucceeded = False
  },

  While[Not[solutionSucceeded] && prec <= maxPrec,

    solutionSucceeded = True; (* Assume it will succeed *)

    (* Assign the input SYT to global variables *)
    \[Lambda]T = SYT;
    \[Lambda] = SYT // ToYD; (* Convert SYT to Young diagram shape *)

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

    (* Try running Iterate *)
    Print["Starting Iterate with precision: ", prec];
    internalOutput = Iterate;

    (* Check if Iterate returned TooSmallStepSize *)
    If[internalOutput === "TooSmallStepSize",
      Print["Iterate returned too small step size. Increasing precision to: ", prec + precIncrement];
      prec += precIncrement;
      SetParameters[maxord, \[CapitalLambda]0, prec, interpord, startinterpord, MyMaxIterations, base, pmin, RecoverySpeed, \[CapitalLambda]target];
      solutionSucceeded = False; (* Mark as unsuccessful and retry *)
    ];
  ];

  (* If max precision is reached, warn the user *)
  If[prec > maxPrec, Print["Maximum precision reached. Could not complete solution."]];

  Print["Solution completed at precision: ", prec];
];



Iterate


(* ::Subsection:: *)
(*Relating to rigged configurations*)


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


(* ::Section:: *)
(*Iterate lazysolver*)


(* ::Subsection::Closed:: *)
(*Old and new StepIterate*)


(* OldStepIterate: Iteration procedure with a fixed step size *)
OldStepIterate[] := Block[{},
  
  (* Iteration process *)
  Iterate := Block[{},
    mPrint["Numerical iterations towards \[CapitalLambda]=", \[CapitalLambda]target];
    mPrint["If step becomes below 10^(-7), try to increase precision"];

    (* Initialize step parameters *)
    pp = pmin; 
    qq = 1;
    step := qq / base^pp;  (* Define step size *)

    (* Start the iteration *)
    \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

    Monitor[
      While[\[CapitalLambda]Last > \[CapitalLambda]target,

        (* Compute new \[CapitalLambda] value *)
        \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
        normedrel = InterpEqns[\[CapitalLambda]new];

        (* Check step size and update values accordingly *)
        Which[
          Catch[FindSol] === "Too big step",
          pp = pp + 1,

          i > 5,
          sol[\[CapitalLambda]new] = minsolrep;
          AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new],

          True,
          sol[\[CapitalLambda]new] = minsolrep;
          AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];

          (* Adjust step control variables dynamically *)
          If[pp > pmin, 
            qq = qq + \[CapitalDelta]q;
            If[qq == base, qq = 1; pp = pp - 1]
          ];
        ];

        (* Update last computed \[CapitalLambda] value *)
        \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
      ],
      
      (* Monitor and display progress *)
      Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
    ] // PrintDone;
  ];
];

(* NewStepIterate: Iteration procedure with adaptive step size *)
NewStepIterate[howcloselambda1_, smalllambda_] := Block[{},
  
  (* Iteration process *)
  Iterate := Block[{},
    mPrint["Numerical iterations towards \[CapitalLambda]=", \[CapitalLambda]target];
    mPrint["If step becomes below 10^(-7), try to increase precision"];

    (* Initialize step parameters *)
    pp = pmin; 
    qq = 1;
    
    (* Define an adaptive step size based on proximity to target *)
    step := Module[{baseStep},
      baseStep = qq / base^pp;
      If[\[CapitalLambda]Last - \[CapitalLambda]target <= howcloselambda1, 
        baseStep / smalllambda,  (* Reduce step size if very close to target *)
        baseStep
      ]
    ];

    (* Start the iteration *)
    \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

    Monitor[
      While[\[CapitalLambda]Last > \[CapitalLambda]target,

        (* Compute new \[CapitalLambda] value *)
        \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
        normedrel = InterpEqns[\[CapitalLambda]new];

        (* Check step size and update values accordingly *)
        Which[
          Catch[FindSol] === "Too big step",
          pp = pp + 1,

          i > 5,
          sol[\[CapitalLambda]new] = minsolrep;
          AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new],

          True,
          sol[\[CapitalLambda]new] = minsolrep;
          AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];

          (* Adjust step control variables dynamically *)
          If[pp > pmin, 
            qq = qq + \[CapitalDelta]q;
            If[qq == base, qq = 1; pp = pp - 1]
          ];
        ];

        (* Update last computed \[CapitalLambda] value *)
        \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
      ],
      
      (* Monitor and display progress *)
      Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, "   step is: ", step // N}]
    ] // PrintDone;
  ];
];



(* ::Subsection:: *)
(*SetParameters*)


SetParameters[
    vmaxord_, vLambda0_, vprec_, vinterpord_, vstartinterpord_, 
    vMyMaxIterations_, vbase_, vpmin_, vRecoverySpeed_, vLambdaTarget_
] := Block[{},
    maxord = vmaxord;
    \[CapitalLambda]0 = vLambda0;
    prec = vprec;
    interpord = vinterpord;
    startinterpord = vstartinterpord;
    $MaxPrecision = Infinity;
    MyMaxIterations = vMyMaxIterations;
    base = vbase;
    pmin = vpmin;
    RecoverySpeed = vRecoverySpeed;
    \[CapitalDelta]q = (base - 1) Min[1, RecoverySpeed];
    \[CapitalLambda]target = vLambdaTarget;
]


(*SetParameters[
    5,          (* maxord *)
    4,          (* \[CapitalLambda]0 *)
    100,        (* prec *)
    40,         (* interpord *)
    15,         (* startinterpord *)
    15,         (* MyMaxIterations *)
    2,          (* base *)
    3,          (* pmin *)
    1/100000,   (* RecoverySpeed *)
    1           (* \[CapitalLambda]target *)
]*)




(* ::Subsection::Closed:: *)
(*FindDuplicateRootPositions*)


FindDuplicateRootPositions[solvedBetheroots_] := Module[
  {
    roundedBetheRoots, tallyBetheRoots, rootMultiplicity, 
    duplicatePositions, duplicateRoots, duplicateRootPositions, 
    duplicateRootPositionsFlatten
  },

  (* Round Bethe roots to 5 decimal places for numerical stability *)
  roundedBetheRoots = Round[solvedBetheroots[[All, 1]], 10^-5]; 

  (* Count occurrences of each rounded root *)
  tallyBetheRoots = Tally[roundedBetheRoots];  

  (* Extract multiplicities of roots *)
  rootMultiplicity = tallyBetheRoots[[All, 2]];  

  (* Identify positions where multiplicity is greater than 1 *)
  duplicatePositions = Flatten[Position[rootMultiplicity, x_ /; x != 1]];  

  (* Extract the actual duplicate root values *)
  duplicateRoots = Table[
    tallyBetheRoots[[k, 1]], {k, duplicatePositions}
  ];  

  (* Find positions of duplicate roots in the original list *)
  duplicateRootPositions = Table[
    Position[roundedBetheRoots, duplicateRoots[[k]]], 
    {k, Length[duplicateRoots]}
  ];  

  (* Flatten the list to return positions in a usable format *)
  duplicateRootPositionsFlatten = Flatten[#, 1] & /@ duplicateRootPositions
]



(* ::Subsection:: *)
(*lazylazySolver*)


lazylazySolver[yd_, riggs_] := Module[
    {
        L, rigs, mySYT, allbetheQ, mysol, allbetherootEqns, solvedBetheroots,
        listCcoefficient, listUmonomial, listUmonomialValue, listUmonomialCoffValue
    },

    (* Compute the total sum of yd *)
    L = Total[yd];

    (* Generate rigged configurations based on yd *)
    rigs = ModestoRiggedConfig[L, #] & /@ ModesConfig[yd];

    (* Convert to Standard Young Tableaux *)
    mySYT = ToSYT /@ rigs;

    (* Initialize list for Bethe equations *)
    allbetheQ = {};

    (* Debugging Print statement *)
    (*Print[riggs];*)

    (* Solve Bethe ansatz from SYT (assumption: `riggs` is an index) *)
    SolutionFromSYT[mySYT[[riggs]]];

    (* Clear previous Print outputs *)
    NotebookDelete[Cells[CellStyle -> "Print"]];

    (* Compute solutions from Bethe ansatz *)
    mysol = Table[YQa[a, 0], {a, Length[\[Lambda] - 1]}] /. 
      First[vars2nvars /. {FindSol[[2]]} /. \[CapitalLambda] -> 1];

    (* Append solution to the list *)
    AppendTo[allbetheQ, mysol];

    (* Generate root equations *)
    allbetherootEqns = Map[# == 0 &, allbetheQ, {2}][[All, 1 ;; 2]];

    (* Solve Bethe root equations *)
    solvedBetheroots = 
      (Table[
        Table[
          Solve[allbetherootEqns[[w]][[k]], u],
          {k, Length[allbetherootEqns[[w]]]}
        ],
        {w, Length[allbetherootEqns]}
      ] // Values) - 1;

    (* Compute coefficient lists for different Lambda values *)
    listCcoefficient = Table[vars2nvars /. \[CapitalLambda] -> \[CapitalLambda]vals[[k]] /. 
        sol[\[CapitalLambda]vals[[k]]], {k, Length[\[CapitalLambda]vals]}];

    (* Compute index vs. Lambda vs. Q-function *)
    listUmonomial = Table[{k, \[CapitalLambda]vals[[k]], 
        Table[YQa[a, 0], {a, Length[\[Lambda]] - 1}]}, 
        {k, Length[\[CapitalLambda]vals]}];

    (* Compute index vs. Lambda vs. Q-function values *)
    listUmonomialValue = MapThread[ReplaceAll, {listUmonomial[[All, 3]], listCcoefficient}];

    (* Extract coefficient values *)
    listUmonomialCoffValue = CoefficientList[listUmonomialValue, u];

    (* Return results *)
    {\[CapitalLambda]vals, solvedBetheroots, listUmonomialCoffValue, listCcoefficient}
]



(* ::Section::Closed:: *)
(*Rigg and mode*)


(* ::Subsection:: *)
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





(* ::Section:: *)
(*Optional but convenience function *)


round[x_, precision_: 10^-5] := Round[x, precision] // N;

mPrint[x___] := Null;


(* ::Subsection:: *)
(*Mute print*)


(* ::Input:: *)
(*PrintDone[x_] := x;*)
(*mPrint[x___] := Null;*)
(*Off[FrontEndObject::notavail]*)


(* ::Input:: *)
(*(* Restore mPrint to print messages *)*)
(*mPrint[x___] := Print[x];*)
(**)
(*(* Restore PrintDone to print timing information *)*)
(*PrintDone[x_] := (Print["...Done in: ", Timing[x][[1]], "s"]; x);*)
(**)


(* ::Section:: *)
(*Test*)


SetParameters[
    5,          (* maxord *)
    4,          (* \[CapitalLambda]0 *)
    90,        (* prec *)
    30,         (* interpord *)
    5,         (* startinterpord *)
    10,         (* MyMaxIterations *)
    2,          (* base *)
    7,          (* pmin *)
    1/1000,   (* RecoverySpeed *)
    1           (* \[CapitalLambda]target *)
]


yd={4,2,1};
L=Total[yd];
rigs=ModestoRiggedConfig[L,#]&/@ModesConfig[yd];
showRC/@rigs;
mySYT=ToSYT/@rigs;
mysol=SolutionFromSYT[mySYT[[1]]]
