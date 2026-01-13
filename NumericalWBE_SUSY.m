(* ::Package:: *)

(* ::Input::Initialization:: *)
SetDirectory[NotebookDirectory[]]
<<"functions.m"
<<"SusyWronskianSolver.m"


(* ::Subsection::Closed:: *)
(*GenerateQsystem*)


(* ::Text:: *)
(*Set up the Q-function and generate the QQ-relations on Young diagram. It relations is given in "Allrel" and corresponds variables is "vars". *)


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



(* ::Subsection:: *)
(*GenerateSUSYWsystem*)


(* ::Input:: *)
(*GenerateSUSYWsystem[yd_]:=Block[{mP,susyresult,LocalYQ\[Theta],mypath,SusyWronskian},*)
(**)
(*	mP={Length@yd,0};*)
(*	mP={1,1};*)
(*	mP=RandomSample[Select[Endpoints[yd], #[[1]] > #[[2]] &],1]//First;*)
(*	mP={Length@yd,0};*)
(*	mP={Length@yd,0};*)
(*	susyresult= GenerateSusyWronskian[mP,yd];*)
(*	SusyWronskian =susyresult[["SusyWronskian"]];*)
(*	LocalYQ\[Theta] = susyresult[["YQ\[Theta]"]];*)
(*	susyvars = Rest[Variables[SusyWronskian]];*)
(*	*)
(*	mypath=Intersection[(Select[ AllPaths[yd], Last[#] === mP & ][[1]]),DomainOfInterest]//Reverse;*)
(*	AllrelWronskian =CoefficientList[YQa[0,0,yd]-Getmonic@SusyWronskian,u]//Expand//(#/.Complex[0,b_]:>b)&;*)
(*	(*susy2ccoefficient*)*)
(*	allsusycoeff = Computesusy2cCoefficients[yd,mypath,mP];*)
(*	(*c2susycoefficient*)*)
(*    c2susycoeff = Computec2susyCoefficients[yd,mypath/.{{0,0}->Nothing}];*)
(*    Print[mP,(allsusycoeff//Keys//Sort)-susyvars];*)
(**)
(*]*)


(* ::Subsection::Closed:: *)
(*init\[Theta]rep*)


(* ::Text:: *)
(*Function to initialize the \[Theta] representation for a given Young tableau \[Lambda]T. This will use in function Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]T_] *)


(* Function to initialize the \[Theta] representation for a given Young tableau \[Lambda]T *)
init\[Theta]rep[\[Lambda]T_] := init\[Theta]rep[\[Lambda]T] = Block[{kk, sd},
  
  (* Initialize the counter function kk *)
  kk[_, _] = 0;
  
  (* unklea *)
  sd[m_] := (Select[#1, #1 <= m &] &) /@ \[Lambda]T;

  (* Check if \[Lambda]T is a standard tableau before proceeding *)
  If[CheckStandard[\[Lambda]T],

    
    Sort[Flatten[
      Table[
        Table[
          If[
            
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
(*Large\[CapitalLambda]ExpansionUptdStart*)


(* ::Item:: *)
(*Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]T_]: Generate "\[CapitalLambda]init\[Theta]repUptd" is use to find "fsymrepUptd"  and "ftransitUptd"*)
(*-  fsymrepUptd replace sym[]->value*)
(*- ftransitUptd c[a,s,k]-> \[CapitalLambda] * value  *)


Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]T_] := Block[
  { \[Lambda], Len},

  (* convert input to Young-diagram list and compute total length *)
  \[Lambda] = \[Lambda]T // ToYD;
  Len = Total[\[Lambda]];

  (* Build initial \[Theta] representation where only the entry with index Max[\[Lambda]T] is set to \[CapitalLambda] *)
  \[CapitalLambda]init\[Theta]repUptd =
    init\[Theta]rep[\[Lambda]T] /. \[Theta][i_] :> If[i == (\[Lambda]T // Max), \[CapitalLambda], 0];
  (* The set of q\[Theta] for the initial \[Lambda]T will be used here *)

  (* fsymrepUptd: mapping sym[n] -> coefficient from the polynomial Product[u,{i,Len-1}] (u - \[CapitalLambda]) *)
  fsymrepUptd = Table[
    sym[n] -> Expand@Coefficient[Product[u, {i, Len - 1}] (u - \[CapitalLambda]), u, Len - n],
    {n, Len}
  ];

  (* ftransitUptd: solve the flattened system of coefficient-list equalities (only for c[a,s,1] in vars2),
     then take the first solution ([[1]]) *)
  ftransitUptd = Solve[
    (
      Table[
        If[
          a + s == 0 || Not@MemberQ[vars2, c[a, s, 1]],
          Nothing,
          CoefficientList[
            YQa[a, s, \[Lambda]] - (YQ\[Theta][a, s, \[Lambda]] /. \[CapitalLambda]init\[Theta]repUptd),
            u
          ]
        ],
        {a, 0, Length[\[Lambda] ] - 1},
        {s, 0, \[Lambda][[a + 1]] - 1}
      ] // Flatten
    ) == 0,
    vars2
  ][[1]];
];



(* ::Subsection::Closed:: *)
(*Large\[CapitalLambda]ExpansionUptdInterim*)


(* ::Item:: *)
(*Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent_, \[Lambda]Tlast_, solninterim_]: Generate "\[CapitalLambda]init\[Theta]repUptd", "fsymrepUptd"  and "ftransitUptd"  *)


Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent_, \[Lambda]Tlast_, solninterim_] := 
Block[{\[Lambda]current, \[Lambda]last, Len},

  \[Lambda]current = \[Lambda]Tcurrent // ToYD;
  \[Lambda]last = \[Lambda]Tlast // ToYD;
  Len = Total[\[Lambda]current];

  
  \[CapitalLambda]init\[Theta]repUptd = 
    init\[Theta]rep[\[Lambda]Tcurrent] /. \[Theta][i_] :> If[i == (\[Lambda]Tcurrent // Max), \[CapitalLambda], 0];

  
  fsymrepUptd = Table[
    sym[n] -> Expand@Coefficient[Product[u, {i, Len - 1}] (u - \[CapitalLambda]), u, Len - n],
    {n, Len}
  ];

  
  ftransitUptdInterim = Solve[
    (
      Table[
        If[
          a + s == 0 || Not@MemberQ[vars2, c[a, s, 1]],
          Nothing,
          CoefficientList[
            YQa[a, s, \[Lambda]current] -
              If[
                a < Position[\[Lambda]Tcurrent, \[Lambda]Tcurrent // Max][[1, 1]] &&
                s < Position[\[Lambda]Tcurrent, \[Lambda]Tcurrent // Max][[1, 2]],
                
                
                (u - Sum[q\[Theta][a, s, k], {k, M[a, s, \[Lambda]current]}]) 
                  YQa[a, s, \[Lambda]last] /. solninterim /. \[CapitalLambda]init\[Theta]repUptd,
                
                
                YQa[a, s, \[Lambda]last] /. solninterim /. \[CapitalLambda]init\[Theta]repUptd
              ],
            u
          ]
        ],
        {a, 0, Length[\[Lambda]current] - 1},
        {s, 0, \[Lambda]current[[a + 1]] - 1}
      ] // Flatten
    ) == 0,
    vars2
  ][[1]];
];




(* ::Subsection::Closed:: *)
(*AsymEqnsUptdStart*)


(* ::Item:: *)
(*AsymEqnsUptdStart[\[CapitalLambda]0_]: Use "fsymrepUptd"  and "ftransitUptd" from Large\[CapitalLambda]Expansion to generating QQ equations using asymptotic approximation*)
(*- ans = normalize QQ relation with "symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0" replaced, which later become normedrel and use in FindMinimum*)
(*- subnc = list of all c[a,s,k], which going use in  FindMinimum to replace vars  *)


(* Generating equations using asymptotic approximation *)
AsymEqnsUptdStart[\[CapitalLambda]0_] := Block[{},
  
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;
  transitUptd = ftransitUptd /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Initial substitution list for c-variables *)
  subnc = transitUptd;
  ans = (# / (1 + Abs[# /. c[a_, s_, k_] :> (c[a, s, k] /. subnc)])) & /@ 
    (Allrel /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand;

  (* Add small randomized perturbations to c[a,s,k] values for numerical stability *)
  subnc = subnc /. (c[a_, s_, k_] -> x_) :> (
    c[a, s, k] -> Rationalize[
      x (1 + Random[]/10^(prec/10)) + Random[]/10^(prec/10),
      10^-prec
    ]
  );

  ans
];





(* ::Subsection::Closed:: *)
(*AsymEqnsUptdInterim*)


(* ::Item:: *)
(*AsymEqnsUptdInterim[\[CapitalLambda]0_]: Use "fsymrepUptd"  and "ftransitUptd" from Large\[CapitalLambda]Expansion to generating QQ equations using asymptotic approximation*)
(*- ans = normalize QQ relation with "symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0" replaced*)
(*- subnc = list of all c[a,s,k]    *)


AsymEqnsUptdInterim[\[CapitalLambda]0_] := Block[{},
  
  
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;
  transitUptdInterim = ftransitUptdInterim /. \[CapitalLambda] -> \[CapitalLambda]0;


  subnc = transitUptdInterim;

  
  ans = (# / (1 + Abs[# /. c[a_, s_, k_] :> (c[a, s, k] /. subnc)])) & /@ 
    (Allrel /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand;

  (* Add small random perturbations to coefficient guesses *)
  subnc = subnc /. (c[a_, s_, k_] -> x_) :> (
    c[a, s, k] -> Rationalize[
      x (1 + Random[]/10^(prec/10)) + Random[]/10^(prec/10),
      10^-prec
    ]
  );

  ans
];


(* ::Subsection::Closed:: *)
(*InterpEqnsUptd*)


(* ::Item:: *)
(*InterpEqnsUptd[\[CapitalLambda]0_] : Generating equations using previous order results and polynomial interpolation*)
(*- ans*)
(*- subnc*)


(* Generating equations using previous order results and polynomial interpolation *)
InterpEqnsUptd[\[CapitalLambda]0_] := Block[
  {minterpord = Min[Length[\[CapitalLambda]vals] - 1, interpord]},

  (* Substitute symbolic expressions with numerical \[CapitalLambda]0 *)
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;

  (* Interpolated substitution for vars using Lagrange polynomial interpolation *)
  subnc = Thread[
    Rule[
      susyvars,
      Rationalize[
        Sum[
          (susyvars /. sol[\[CapitalLambda]vals[[-j]]]) *
          Product[
            If[j == j2, 1, 
              (\[CapitalLambda]0 - \[CapitalLambda]vals[[-j2]]) /
              (\[CapitalLambda]vals[[-j]] - \[CapitalLambda]vals[[-j2]])
            ],
            {j2, minterpord}
          ],
          {j, minterpord}
        ],
        10^-prec
      ]
    ]
  ];

  (* Build interpolated and normalized equation list from Allrel *)
(*  ans = (# / (# /. SUSYc[a_List, b_List][q_] :> (1 + Random[]/10000) SUSYc[a, b][q])) & /@ 
    (AllrelWronskian /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand;*)
  ans = (AllrelWronskian /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand;

    


  (* Slightly randomize the interpolated coefficient values for robustness *)
(*  subnc = subnc /. (SUSYc[a_List, b_List][q_] -> x_) :> (
    SUSYc[a, b][q] -> Rationalize[
      x (1 + Random[]/10^(prec/10)) + Random[]/10^(prec/10),
      10^-prec
    ]
  );*)
  subnc = subnc /. (SUSYc[a_List, b_List][q_] -> x_) :> (
  SUSYc[a, b][q] -> Rationalize[x, 10^-prec]
);

  ans
];




(* ::Subsection::Closed:: *)
(*FindSolUptd*)


(* ::Item:: *)
(*FindSolUptd: FindMinimum of "normedrel . normedrel" with variable "vars"*)
(*- minsolrep*)


FindSolUptdAsymptW := Block[{},
  {
    minim, minsolrep
  } = Quiet@FindMinimum[
    normedrel . normedrel,
    {vars, vars /. subnc} // Transpose,
    WorkingPrecision -> prec,
    PrecisionGoal -> prec,
    AccuracyGoal -> prec/2,
    MaxIterations -> \[Infinity]
  ];
  
];


(* ::Subsection::Closed:: *)
(*FindSolUptdW*)


FindSolUptdW := Block[{interstep},
  interstep = {};
  
  minsolrep = Quiet@FindRoot[
    normedrel,
    {susyvars, susyvars /. subnc} // Transpose,
    WorkingPrecision   -> prec,
    PrecisionGoal      -> prec,
    AccuracyGoal       -> prec/2,
    MaxIterations      -> \[Infinity],
    EvaluationMonitor  :> (AppendTo[interstep, susyvars])
  ];
  (*AppendTo[Steps, interstep];*)
];



(* ::Subsection::Closed:: *)
(*GenerateSolsFromAsymptoticsUptdStart*)


(* ::Item:: *)
(*GenerateSolsFromAsymptoticsUptdStart: (Not need to change)*)


coeff2root[YD_]:=Table[If[{a,s}!={0,0},Thread[CoefficientList[YQa[a,s,YD],u][[;;-2]]->CoefficientList[YQprod[a,s,YD],u][[;;-2]]],Nothing],{a,0,Length[YD]-1},{s,0,YD[[a+1]]-1}]//Flatten;
rootsfromcoeff[YD_,sol_]:=Block[{k},Table[If[{a,s}!={0,0},k=1;ReplaceAll[#,u->x[a,s,k++]]&/@(NSolve[YQa[a,s,YD]/.sol,u]//Flatten),Nothing],{a,0,Length[YD]-1},{s,0,YD[[a+1]]-1}]//Flatten];
(* generating first sample points for interpolation to work + some large \[CapitalLambda] expressions *)

GenerateSolsFromAsymptoticsUptdStart[\[Lambda]current_] := Block[{},
  
  \[CapitalLambda]vals0 = {};
  
  \[CapitalLambda]0 = IntegerPart[Sqrt[Total@\[Lambda]current] + 1];
 (* \[CapitalLambda]0 = \[CapitalLambda]0Interim;*)
  (* IS THERE A BETTER WAY TO SET \[CapitalLambda]0 HERE? *)
  (*\[CapitalLambda]0 = 1000;*)
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) * 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;
  
  Monitor[
    Do[
      normedrel = AsymEqnsUptdStart[\[CapitalLambda]0];
      FindSolUptdAsymptW;

      (* sol[\[CapitalLambda]0] := Thread[Rule[vars2, (vars2 /. subc)(vars3 /. minsolrep)]]; *)
      sol[\[CapitalLambda]0] = allsusycoeff/.minsolrep/.symrepUptd;
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];
      ,
      {\[CapitalLambda]0, rng}
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}]
  ]
  
];





(* ::Subsection::Closed:: *)
(*GenerateSolsFromAsymptoticsUptdInterim*)


(* ::Item:: *)
(*GenerateSolsFromAsymptoticsUptdInterim: (contain lambda0)*)


GenerateSolsFromAsymptoticsUptdInterim[\[Lambda]current_, \[Lambda]last_, coefflast_] := Block[{},
  
  \[CapitalLambda]vals0 = {};
  \[CapitalLambda]0 = \[CapitalLambda]0Interim;
  
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) * 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;
  
  Monitor[
    Do[
      normedrel = AsymEqnsUptdInterim[\[CapitalLambda]0];
      
      FindSolUptdAsymptW;

      (* sol[\[CapitalLambda]0] := Thread[Rule[vars2, (vars2 /. subc)(vars3 /. minsolrep)]]; *)
      sol[\[CapitalLambda]0] = allsusycoeff/.minsolrep/.symrepUptd;
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];
      ,
      {\[CapitalLambda]0, rng}
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}]
  ]
  
];


(* ::Subsection::Closed:: *)
(*IterateUptdStart*)


(* ::Item:: *)
(*IterateUptdStart: (contain step)*)


IterateUptdStart[SYT_] := Block[{},

  (* \[CapitalLambda]Last is the most recent \[CapitalLambda] value *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
  
  step = 0.1; (* override step size if desired *)

  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,
    
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
      
      normedrel = InterpEqnsUptd[\[CapitalLambda]new];
      FindSolUptdW;
      
      
      sol[\[CapitalLambda]new] = minsolrep;
      AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];
      
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
    ],
    
    Row@{
      "Current \[CapitalLambda] history is: ", \[CapitalLambda]vals // N,
      " current \[CapitalLambda] is: ", \[CapitalLambda]Last // N,
      " step is: ", step // N
    }
  ];
  
];


(* ::Subsection::Closed:: *)
(*IterateUptdInterim (NoNeed)*)


(* ::Item:: *)
(*IterateUptdInterim: (contain step)*)


residualList = {};
IterateUptdInterim[SYT_] := Block[{},
  
  (* \[CapitalLambda]Last is the most recent \[CapitalLambda] value *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];


  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,
    

	  stepblock;
  
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];
      
      normedrel = InterpEqnsUptd[\[CapitalLambda]new];
      
      (*PrintTemporary[\[CapitalLambda]new,"StartFindSolUptdW"];*)
      FindSolUptdW;
      (*PrintTemporary[\[CapitalLambda]new,"DoneFindSolUptdW"];*)
      

      sol[\[CapitalLambda]new] = minsolrep;
      
      AppendTo[predictorCorrectorList,{\[CapitalLambda]new,subnc,minsolrep}];
      AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];
      
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
    ],
    
    Row@{
      "Current \[CapitalLambda] history is: ", \[CapitalLambda]vals // N,
      " current \[CapitalLambda] is: ", \[CapitalLambda]Last // N,
      " step is: ", step // N
    }
  ];
  
];



(* ::Subsection:: *)
(*IterateUptdInterimJulia*)


MyFindRoot := Block[{interstep},
  interstep = {};
  
  MYminsolrep = Quiet@FindRoot[
    InterpEqnsUptd[\[CapitalLambda]0],
    sol[\[CapitalLambda]0] /. Rule[b_, val_] :> {b,val},
    WorkingPrecision   -> prec,
    PrecisionGoal      -> prec,
    AccuracyGoal       -> prec,
    MaxIterations      -> \[Infinity],
    EvaluationMonitor  :> (AppendTo[interstep, susyvars])
  ];
  
  (*AppendTo[Steps, interstep];*)
];


makeStr[list_]:=StringJoin[ToString/@list];
exportToJuliaInitialData[SYT_]:=Block[{},
(* Expression conversion *)
myFunc = (InterpEqnsUptd[h]);
convertExprs = (myFunc// ExpandAll) /. SUSYc[a_List, b_List][q_] :> 
   Symbol[
    "SUSYc" <> 
     makeStr[a] <>   (* First list content *)
     "X" <>          (* SEPARATOR: Ensures uniqueness *)
     makeStr[b] <>   (* Second list content *)
     "M" <>          (* Separator for the q index *)
     ToString[q]
    ];
cleanExprs = ToString[#, InputForm] & /@ convertExprs;
cleanExprs = StringReplace[#, "*^" -> "*10^"] & /@ cleanExprs;

(* Expression Jacobian *)
convertJacobian = (D[myFunc,{susyvars}]// ExpandAll) /. SUSYc[a_List, b_List][q_] :> 
   Symbol[
    "SUSYc" <> 
     makeStr[a] <>   (* First list content *)
     "X" <>          (* SEPARATOR: Ensures uniqueness *)
     makeStr[b] <>   (* Second list content *)
     "M" <>          (* Separator for the q index *)
     ToString[q]
    ];
cleanJacobian = ToString[#, InputForm] & /@ convertJacobian;
cleanJacobian = StringReplace[#, "*^" -> "*10^"] & /@ cleanJacobian;

(* Variable conversion *)
convertVars = susyvars   /. SUSYc[a_List, b_List][q_] :> 
   Symbol[
    "SUSYc" <> 
     makeStr[a] <>   (* First list content *)
     "X" <>          (* SEPARATOR: Ensures uniqueness *)
     makeStr[b] <>   (* Second list content *)
     "M" <>          (* Separator for the q index *)
     ToString[q]
    ];
cleanVars = ToString /@ convertVars;

(* Initial values *)
MyFindRoot;
MYminsolrep;
(*initb = Values[sol[\[CapitalLambda]0]];*)
initb = (MYminsolrep//Values);
(*initb = Values[sol[\[CapitalLambda]0]];*)
cleanInitb = ToString[N[#, prec], InputForm] & /@ initb;
cleanInitb = StringReplace[#, "*^" -> "*10^"] & /@ cleanInitb;
cleanInitb = StringReplace[cleanInitb, "`" <> ToString[prec] <> "." -> ""];
(*cleanInitb = StringReplace[cleanInitb, "`." -> ""];*)
(* Check lengths *)
{Length[cleanExprs], Length[cleanVars], Length[cleanInitb]};

(* Combine and export *)
table = Transpose[{
	ConstantArray[SYT,Length[cleanExprs]],
	ConstantArray[\[CapitalLambda]0,Length[cleanExprs]],
	cleanVars, 
	cleanInitb, 
	cleanExprs,
	cleanJacobian}];
(*Export["/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/initial_data.csv",
  Prepend[table, {"var", "Initialvar","expression"}]];*)
  
mytable =  {"syt","lambda0","var", "Initialvar", "expression","jacobian"};

Export["saved_data/initial_data.csv", Prepend[table, mytable]];

filename = "saved_data/" <> ToString[SYT] <> ".csv";
filename = "saved_data/" <> ToString[mP] <> "_"<>ToString[SYT]<>".csv";
Export[filename, Prepend[table, mytable]]

]



juliaInputNew[SYT_, \[CapitalLambda]0Interim_] :=" 

Base.include(Main, \"/home/zuxian/Documents/BAE/HomotopyContinuation_BAE.jl\")

"
(*juliaOutput = ExternalEvaluate[sessionJulia,juliaInputNew[we, \[CapitalLambda]0Interim]]*)


sessionJulia=StartExternalSession["Julia"];


IterateUptdInterimJulia[SYT_]:=Block[{},
 exportToJuliaInitialData[SYT];
 Print["Initial norm: ",Norm[InterpEqnsUptd[\[CapitalLambda]0]/.sol[\[CapitalLambda]0]]];
 Print["First findroot norm: ",Norm[(InterpEqnsUptd[\[CapitalLambda]0]// ExpandAll)/.MYminsolrep]];

 (*juliaOutput = SetPrecision[ExternalEvaluate[sessionJulia,juliaInputNew[SYT,\[CapitalLambda]0Interim]],prec]*);
 
 juliaOutput = Quiet @ Check[
  SetPrecision[ExternalEvaluate[sessionJulia, juliaInputNew[SYT, \[CapitalLambda]0Interim]], prec],
  $Failed
];

If[!(ListQ[juliaOutput] && VectorQ[juliaOutput, NumericQ]),
  Throw[Nothing, "BadJuliaOutput"];
];


 minsolrep=Rule@@@Transpose[{susyvars,SetPrecision[juliaOutput,prec]}];
 sol[0]=minsolrep;
 AppendTo[\[CapitalLambda]vals,0];
(* juliaTime = ExternalEvaluate[sessionJulia,"[time_dummy,time_final]"];
 AppendTo[savedJuliaTime,juliaTime];*)
]


(* ::Subsection::Closed:: *)
(*SolutionFromSYTUptdStart*)


(* ::Item:: *)
(*SolutionFromSYTUptdStart:*)


Ccoeff := Block[{},
  (*ccoeffat0 = c2susycoeff /. sol[0]//Flatten;*)
  ccoeffat0 =Select[c2susycoeff /. sol[0]//Flatten,Chop[Im[Last[#]]]==0&]//Chop;
  eqsrel = Allrel /. ccoeffat0 /. fsymrepUptd /. \[CapitalLambda] -> 0;
  eqsrelred = Select[(eqsrel // Chop), !(# === 0) &];
  
  If[(Length[eqsrelred] > 0),
    ccoeffsolvedat0 = FindMinimum[
      eqsrel . eqsrel,
      Variables[eqsrel]
    ][[2]];
    
    AppendTo[ccoeffat0, ccoeffsolvedat0] // Flatten,
    
    ccoeffat0
  ]
]




SolutionFromSYTUptdStart[SYT_] := Block[{
    \[Lambda]Tstart, \[Lambda]start
  },
  
  (* Solve the initial YT \[LongDash] one row with increasing tableau values and one box in the next row *)
  Steps = {};
  
  \[Lambda]Tstart = SYT;
  \[Lambda]start = \[Lambda]Tstart // ToYD;
  
  GenerateQsystem[\[Lambda]start];
  GenerateSUSYWsystem[\[Lambda]start];
  Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]Tstart];
  GenerateSolsFromAsymptoticsUptdStart[\[Lambda]start];
  
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  
  IterateUptdStart[\[Lambda]Tstart];
  
  currentsol = {
    \[CapitalLambda]vals,
    sol[\[CapitalLambda]vals[[#]]] & /@ Range[1, Length[\[CapitalLambda]vals]],
    Ccoeff
  }
]




(* ::Subsection:: *)
(*SolutionFromSYTUptdInterim*)


SolutionFromSYTUptdInterim[SYTcurrent_, SYTlast_, solnlast_] := Block[{
    \[Lambda]Tcurrent, \[Lambda]Tlast, \[Lambda]current, \[Lambda]last
  },
  
  Steps = {};
  
  \[Lambda]Tcurrent = SYTcurrent;
  \[Lambda]Tlast = SYTlast;
  
  \[Lambda]current = \[Lambda]Tcurrent // ToYD;
  \[Lambda]last = \[Lambda]Tlast // ToYD;
  
  GenerateQsystem[\[Lambda]current];
  GenerateSUSYWsystem[\[Lambda]current];
  Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent, \[Lambda]Tlast, solnlast];
  GenerateSolsFromAsymptoticsUptdInterim[\[Lambda]current, \[Lambda]last, solnlast];
  
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  
  
  Print["startJulia: ", SYTcurrent];
  (*IterateUptdInterim[\[Lambda]Tcurrent];*)
  $CurrentIterator[\[Lambda]Tcurrent];
  

  
  currentsol = {
    \[CapitalLambda]vals,
    sol[\[CapitalLambda]vals[[#]]] & /@ Range[1, Length[\[CapitalLambda]vals]],
    Ccoeff
  }
]


(* ::Subsection::Closed:: *)
(*SolutionFromSYTUptdStepwiseWronskian*)


SolutionFromSYTUptdStepwiseWronskian[SYT_] := Catch[
  Block[{ \[Lambda]Tlist },
    StepsStepwise = {};
    ansWholeIteration = {};
    predictorCorrectorList = {};
    
    \[Lambda]Tlist = Table[
      Select[MemberQ[Range[1, i], #] &] /@ SYT /. {{} -> Nothing},
      {i, Count[SYT[[1]] - Range[Length[SYT[[1]]]], 0], Max[SYT]}
    ][[2 ;;]];
    
    SolutionFromSYTUptdStart[\[Lambda]Tlist[[1]]];
    AppendTo[StepsStepwise, {
      \[CapitalLambda]vals[[#]],
      Thread[susyvars -> #] & /@ Steps[[#]]
    } & /@ Range[Length[Steps]]];
    AppendTo[ansWholeIteration, currentsol];
    
   (* ClearAll[EvalQFunction];
    <<"SusyWronskianSolver.m"//Quiet;*)
    Do[
      Module[{ \[Lambda]Tcurrent, \[Lambda]Tlast },
        \[Lambda]Tcurrent = \[Lambda]Tlist[[i]];
        \[Lambda]Tlast = \[Lambda]Tlist[[i - 1]];
        
        SolutionFromSYTUptdInterim[\[Lambda]Tcurrent, \[Lambda]Tlast, currentsol[[3]]];
        
        AppendTo[StepsStepwise, {
          \[CapitalLambda]vals[[#]],
          Thread[susyvars -> #] & /@ Steps[[#]]
        } & /@ Range[Length[Steps]]];
        
        AppendTo[ansWholeIteration, currentsol];
        
      ];
     (* ClearAll[EvalQFunction];
    <<"SusyWronskianSolver.m"//Quiet;*)
    ,
      {i, 2, Length[\[Lambda]Tlist]}
    ];
    
    ansWholeIteration
  ],
  "BadJuliaOutput"
];


(* ::Subsection::Closed:: *)
(*Run Test*)


(* ::Subitem:: *)
(*singleSYTresult*)


singleSYTresult[yd_, k_] := Block[{},
  \[CapitalLambda]0Interim = 100;
  \[CapitalLambda]target = 0;
  startinterpord = 2;
  prec = 40;
  interpord = 1;

  ansWprov = Which[
    IntegerQ[k],
    L = Total[yd];
    modes = ModesConfig[yd];
    rig = ModestoRiggedConfig[L, modes[[k]]];
    mySYT = ToSYT[rig];
    SolutionFromSYTUptdStepwiseWronskian[mySYT],
    k === "rand",
    myrandTableau = RandomTableau[yd];
      SolutionFromSYTUptdStepwiseWronskian[myrandTableau],
    True,
      (Print["Invalid input for k"]; $Failed)
  ];
]


(* ::Subitem:: *)
(*singleSYTresultUNIK*)


singleSYTresultUNIK[SYT_] := Block[{},
  \[CapitalLambda]0Interim = 20;
  \[CapitalLambda]target = 0;
  startinterpord = 2;
  prec = 100;
  interpord = 3;
  ansWprov = SolutionFromSYTUptdStepwiseWronskian[SYT];
]


(* ::Subitem:: *)
(*RandomPartitionWithLength*)


RandomPartitionWithLength[L_, n_] := Module[{parts},
  parts = Select[IntegerPartitions[L], Length[#] == n &];
  If[parts === {}, 
    Missing["NotAvailable"], 
    RandomChoice[parts]
  ]
]


singleSYTresultOUTPUT[yd_, modes_] := Block[{},
  \[CapitalLambda]0Interim = 10;
  \[CapitalLambda]target = 0;
  startinterpord = 2;
  prec = 40;
  interpord = 1;


  rig = ModestoRiggedConfig[L, modes];
  mySYT = ToSYT[rig];
  ansWprov =SolutionFromSYTUptdStepwiseWronskian[mySYT]
]



(* ::Input:: *)
(*<<"SusyWronskianSolver.m"*)
(*GenerateSUSYWsystem[yd_]:=Block[{mP,susyresult,LocalYQ\[Theta],mypath,SusyWronskian},*)
(*         mP=RandomSample[Select[Endpoints[yd], #[[1]] > #[[2]] &],1]//First;*)
(*	mP={Length@yd,0};*)
(*	susyresult= GenerateSusyWronskian[mP,yd];*)
(*	SusyWronskian =susyresult[["SusyWronskian"]];*)
(*	LocalYQ\[Theta] = susyresult[["YQ\[Theta]"]];*)
(*	susyvars = Rest[Variables[SusyWronskian]];*)
(*	*)
(*	mypath=Intersection[(Select[ AllPaths[yd], Last[#] === mP & ][[1]]),DomainOfInterest]//Reverse;*)
(*	AllrelWronskian =CoefficientList[YQa[0,0,yd]-Getmonic@SusyWronskian,u]//Expand//(#/.Complex[0,b_]:>b)&;*)
(*	(*susy2ccoefficient*)*)
(*	allsusycoeff = Computesusy2cCoefficients[yd,mypath,mP];*)
(*	(*c2susycoefficient*)*)
(*    c2susycoeff = Computec2susyCoefficients[yd,mypath/.{{0,0}->Nothing}];*)
(*    Print[mP,(allsusycoeff//Keys//Sort)-susyvars];*)
(**)
(*]*)


(* ::Input:: *)
(*yd ={4,2,1};*)
(*randsyt=yd//RandomTableau*)
(*randsyt = ({4,2,1}//Tableaux)[[3]]*)
(*randsyt ={{1,2,3,5},{4,7},{6}};*)
(**)
(*yd ={4,2,1};*)
(*randsyt=yd//RandomTableau*)
(*randsyt ={{1,2,3,4},{5,7},{6}};*)
(**)
(*yd ={4,1,1};*)
(**)
(*randsyt=yd//RandomTableau*)
(*singleSYTresultUNIK[randsyt]*)


(* ::Input:: *)
(*GenerateSUSYWsystem[yd_]:=Block[{mP,susyresult,LocalYQ\[Theta],mypath,SusyWronskian},*)
(**)
(*	mP={1,1};*)
(*	mP=RandomSample[Select[Endpoints[yd], #[[1]] > #[[2]] &],1]//First;*)
(*mP={Length@yd,0};*)
(*	susyresult= GenerateSusyWronskian[mP,yd];*)
(*	SusyWronskian =susyresult[["SusyWronskian"]];*)
(*	LocalYQ\[Theta] = susyresult[["YQ\[Theta]"]];*)
(*	susyvars = Rest[Variables[SusyWronskian]];*)
(*	*)
(*	mypath=Intersection[(Select[ AllPaths[yd], Last[#] === mP & ][[1]]),DomainOfInterest]//Reverse;*)
(*	AllrelWronskian =CoefficientList[YQa[0,0,yd]-Getmonic@SusyWronskian,u]//Expand//(#/.Complex[0,b_]:>b)&;*)
(*	(*susy2ccoefficient*)*)
(*	allsusycoeff = Computesusy2cCoefficientsv2[yd,mP];*)
(*	(*c2susycoefficient*)*)
(*    c2susycoeff = Computec2susyCoefficients[yd,DomainOfInterest//Rest//Reverse];*)
(*    Print[mP,(allsusycoeff//Keys//Sort)-susyvars];*)
(**)
(*]*)
(**)
(**)
(*randsyt ={{1,2,3,4},{5,7},{6}};*)
(**)
(*yd ={4,2,1};*)
(**)
(*randsyt=yd//RandomTableau*)
(*singleSYTresultUNIK[randsyt]*)


(* ::Input:: *)
(*Total@(NumberOfTableaux/@IntegerPartitions[#])&/@Range[20]*)
(*ListLogLogPlot[%]*)


ConvertFromCoefficientToRoots[solc_] := Module[
  {solList, allBetheQ, allBetheRootEqns, betheRoots},
  
  solList = If[ MatchQ[solc, {(_Rule)...}],
                {solc},     
                solc         
             ];

  Map[
    Function[sol,
      (* apply the solution to the Bethe equations *)
      allBetheQ = Table[YQa[w, 0, yd], {w, Length[yd] - 1}] /. sol;
      allBetheRootEqns = Thread[allBetheQ == 0];

      (* solve each equation for u *)
      betheRoots = Map[
        Function[eqn,
          Module[{r = Solve[eqn, u]},
            If[r === {}, Missing["NoSolution"], u /. r]
          ]
        ],
        allBetheRootEqns
      ];

      betheRoots
    ],
    solList
  ]
]

