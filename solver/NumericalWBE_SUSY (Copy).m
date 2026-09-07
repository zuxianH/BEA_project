(* ::Package:: *)

(* Numerical continuation and root-finding routines for the SUSY Wronskian
   workflow. High-level orchestration now lives in SUSYWBEWorkflow.wl. *)

ClearAll[SUSYWBEPackageDirectory];
SUSYWBEPackageDirectory[] := Module[
  {projectDirectory, inputDirectory, notebookDirectory},
  projectDirectory = Which[
    ValueQ[$SUSYWBEProjectRoot] && StringQ[$SUSYWBEProjectRoot] && DirectoryQ[$SUSYWBEProjectRoot],
    $SUSYWBEProjectRoot,
    ValueQ[SUSYWBEProjectDirectory],
    Quiet@Check[SUSYWBEProjectDirectory[], $Failed],
    True,
    $Failed
  ];
  inputDirectory = If[
    StringQ[$InputFileName] && $InputFileName =!= "",
    DirectoryName[$InputFileName],
    $Failed
  ];
  notebookDirectory = Quiet[
    Check[NotebookDirectory[], $Failed],
    FrontEndObject::notavail
  ];

  SelectFirst[
    Replace[
      {projectDirectory, inputDirectory, notebookDirectory, Directory[]},
      path_String :> If[
        DirectoryQ[path] && MemberQ[{"solver", "utils", "julia"}, FileNameTake[path]],
        DirectoryName[path],
        path
      ],
      {1}
    ],
    StringQ[#] && DirectoryQ[#] &,
    Directory[]
  ]
];

ClearAll[SUSYWBEUtilsDirectory, SUSYWBESolverDirectory, SUSYWBEJuliaDirectory];
SUSYWBEUtilsDirectory[] := FileNameJoin[{SUSYWBEPackageDirectory[], "utils"}];
SUSYWBESolverDirectory[] := FileNameJoin[{SUSYWBEPackageDirectory[], "solver"}];
SUSYWBEJuliaDirectory[] := FileNameJoin[{SUSYWBEPackageDirectory[], "julia"}];

Get[FileNameJoin[{SUSYWBEUtilsDirectory[], "functions.m"}]];
Get[FileNameJoin[{SUSYWBESolverDirectory[], "SusyWronskianSolver.m"}]];

SolutionFromSYTUptdStart::usage =
  "SolutionFromSYTUptdStart[syt] solves the initial tableau in the stepwise SUSY Wronskian workflow.";

SolutionFromSYTUptdInterim::usage =
  "SolutionFromSYTUptdInterim[current, previous, coeffs] advances one tableau step in the stepwise SUSY Wronskian workflow.";

SolutionFromSYTUptdStepwiseWronskian::usage =
  "SolutionFromSYTUptdStepwiseWronskian[syt] solves the full tableau by growing it stepwise.";

IterateUptdInterim::usage =
  "IterateUptdInterim[syt] applies the Mathematica-based predictor-corrector continuation.";

IterateUptdInterimJulia::usage =
  "IterateUptdInterimJulia[syt] applies the Julia-assisted continuation backend.";

ConvertFromCoefficientToRoots::usage =
  "ConvertFromCoefficientToRoots[coeffs] converts a coefficient solution to Bethe roots using the current global yd.";



(* ::Subsection:: *)
(*GenerateSUSYWsystem*)


(* GenerateSUSYWsystem is now provided by SUSYWBEWorkflow.wl so the numerical
   routines can consume a single, documented system-construction entry point. *)

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
  
  If[! NumericQ[step], step = 0.1];

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
  If[! NumericQ[step], step = 0.1];


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
runConfiguration = GetJuliaRunConfiguration[];
savedDataDir = runConfiguration["SavedDataDir"];
initialDataFile = runConfiguration["InitialDataFile"];
If[! DirectoryQ[savedDataDir],
  CreateDirectory[savedDataDir, CreateIntermediateDirectories -> True]
];

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

Export[
  initialDataFile,
  Prepend[table, mytable]
];

If[TrueQ[Lookup[runConfiguration, "SaveSubSYTCSVFiles", True]],
  filename = FileNameJoin[{
    savedDataDir,
    ToString[mP] <> "_" <> ToString[SYT] <> ".csv"
  }];
  Export[filename, Prepend[table, mytable]]
]

]



juliaInputNew[SYT_, \[CapitalLambda]0Interim_] :=
  Module[{runConfiguration, scriptPath, moduleName, moduleCode},
    runConfiguration = GetJuliaRunConfiguration[];
    scriptPath = FileNameJoin[{SUSYWBEJuliaDirectory[], "HomotopyContinuation_BAE.jl"}];
    moduleName = StringReplace[
      "SUSYWBEJuliaRun" <> CreateUUID[],
      "-" -> ""
    ];
    moduleCode = StringRiffle[
      {
        "module " <> moduleName,
        "const BAE_SAVED_DATA_DIR = " <> ToString[runConfiguration["SavedDataDir"], InputForm],
        "const BAE_INITIAL_DATA_FILE = " <> ToString[runConfiguration["InitialDataFile"], InputForm],
        "const BAE_OUTPUT_FILE = " <> ToString[runConfiguration["OutputFile"], InputForm],
        "const BAE_TIMING_FILE = " <> ToString[runConfiguration["JuliaTimingFile"], InputForm],
        "const BAE_FINAL_OUTPUT = include(" <> ToString[scriptPath, InputForm] <> ")",
        "end"
      },
      "\n"
    ];
    StringRiffle[
      {
        "begin",
        "Base.include_string(Main, " <> ToString[moduleCode, InputForm] <> ")",
        "nothing",
        "end"
      },
      "\n"
    ]
  ];
(*juliaOutput = ExternalEvaluate[sessionJulia,juliaInputNew[we, \[CapitalLambda]0Interim]]*)


ClearAll[NormalizeJuliaBackend];
NormalizeJuliaBackend[backend_] := Replace[
  backend,
  {
    Automatic -> "ProcessPerRun",
    "CLI" -> "ProcessPerRun",
    "ExternalSession" -> "PersistentSession"
  }
];


ClearAll[PersistentJuliaBackendQ];
PersistentJuliaBackendQ[backend_] := MemberQ[
  {"PersistentSession", "PersistentSessionSysimage"},
  NormalizeJuliaBackend[backend]
];


ClearAll[JuliaProcessFlagsList];
JuliaProcessFlagsList[runConfiguration_Association] := Replace[
  Lookup[runConfiguration, "JuliaProcessFlags", {"--threads=1"}],
  Except[_List] :> {"--threads=1"}
];


ClearAll[JuliaSysimageArgument];
JuliaSysimageArgument[runConfiguration_Association] := Module[
  {backend, sysimagePath},
  backend = NormalizeJuliaBackend[Lookup[runConfiguration, "JuliaBackend", "ProcessPerRun"]];
  sysimagePath = Lookup[runConfiguration, "JuliaSysimagePath", None];
  If[
    backend === "PersistentSessionSysimage" &&
    StringQ[sysimagePath] &&
    FileExistsQ[sysimagePath],
    {"-J", sysimagePath},
    {}
  ]
];


ClearAll[SUSYWBEJuliaExecutable];
ClearAll[JuliaExecutableFromUserShell, PlainJuliaRunConfiguration, StartPersistentJuliaWorker];
JuliaExecutableFromUserShell[] := Module[
  {shellPath, shellResult, shellOutput},
  If[$OperatingSystem === "Windows",
    Return[$Failed]
  ];

  shellPath = Quiet@Check[Environment["SHELL"], ""];
  If[! StringQ[shellPath] || StringTrim[shellPath] === "",
    Return[$Failed]
  ];

  shellResult = Quiet @ Check[
    RunProcess[{shellPath, "-lc", "command -v julia"}, All],
    $Failed
  ];
  shellOutput = StringTrim @ Replace[
    shellResult,
    {
      result_Association :> Lookup[result, "StandardOutput", ""],
      _ :> ""
    }
  ];

  If[StringQ[shellOutput] && shellOutput =!= "" && FileExistsQ[shellOutput],
    shellOutput,
    $Failed
  ]
];

SUSYWBEJuliaExecutable[runConfiguration_: Automatic] := Module[
  {homeDirectory, configuredExecutable, discoveredExecutable},
  homeDirectory = Quiet@Check[HomeDirectory[], $HomeDirectory];
  configuredExecutable = Replace[
    If[AssociationQ[runConfiguration], Lookup[runConfiguration, "JuliaExecutable", Automatic], Automatic],
    {
      Automatic -> Automatic,
      path_String /; StringTrim[path] === "" :> Automatic,
      path_String /; StringContainsQ[path, "/"] || StringContainsQ[path, "\\"] || StringStartsQ[path, "."] :> ExpandFileName[path],
      path_String :> StringTrim[path]
    }
  ];
  discoveredExecutable = Quiet@Check[FindExecutable["julia"], $Failed];
  SelectFirst[
    DeleteDuplicates @ Cases[
      {
        configuredExecutable,
        Environment["JULIA"],
        discoveredExecutable,
        JuliaExecutableFromUserShell[],
        If[StringQ[homeDirectory], FileNameJoin[{homeDirectory, ".juliaup", "bin", "julia"}], Nothing],
        If[StringQ[homeDirectory], FileNameJoin[{homeDirectory, ".local", "bin", "julia"}], Nothing],
        "/usr/local/bin/julia",
        "/usr/bin/julia",
        "/opt/homebrew/bin/julia",
        "/snap/bin/julia",
        "julia"
      },
      _String
    ],
    If[# === "julia", True, FileExistsQ[#]] &,
    "julia"
  ]
];


ClearAll[BuildJuliaCommand];
BuildJuliaCommand[scriptPath_String, runConfiguration_Association] := Join[
  {SUSYWBEJuliaExecutable[runConfiguration]},
  JuliaProcessFlagsList[runConfiguration],
  JuliaSysimageArgument[runConfiguration],
  {
    "--project=" <> SUSYWBEPackageDirectory[],
    scriptPath
  }
];


ClearAll[PersistentJuliaWorkerRunningQ];
PersistentJuliaWorkerRunningQ[] := TrueQ[
  ValueQ[$SUSYWBEPersistentJuliaWorker] &&
  MatchQ[$SUSYWBEPersistentJuliaWorker, _ProcessObject] &&
  Quiet@Check[ProcessStatus[$SUSYWBEPersistentJuliaWorker] === "Running", False]
];


ClearAll[ReadJuliaWorkerLine];
ReadJuliaWorkerLine[process_ProcessObject, timeout_?NumericQ] := Quiet @ Check[
  TimeConstrained[ReadLine[process], timeout, $Aborted],
  $Failed
];


ClearAll[PersistentJuliaWorkerKey];
PersistentJuliaWorkerKey[runConfiguration_Association] := {
  NormalizeJuliaBackend[Lookup[runConfiguration, "JuliaBackend", "ProcessPerRun"]],
  JuliaProcessFlagsList[runConfiguration],
  Lookup[runConfiguration, "JuliaSysimagePath", None],
  Lookup[runConfiguration, "JuliaExecutable", Automatic]
};


PlainJuliaRunConfiguration[runConfiguration_Association] := Join[
  runConfiguration,
  <|
    "JuliaBackend" -> "PersistentSession",
    "JuliaSysimagePath" -> None
  |>
];


StartPersistentJuliaWorker[runConfiguration_Association] := Module[
  {workerPath, timeout, workerCommand, process, readyLine, readyParts, startupSeconds},
  workerPath = FileNameJoin[{SUSYWBEJuliaDirectory[], "SUSYWBEPersistentWorker.jl"}];
  timeout = Lookup[runConfiguration, "JuliaTimeout", 900];
  workerCommand = BuildJuliaCommand[workerPath, runConfiguration];

  process = Quiet @ Check[StartProcess[workerCommand], $Failed];
  If[process === $Failed,
    Return[$Failed]
  ];

  readyLine = ReadJuliaWorkerLine[process, timeout];
  If[readyLine === $Aborted || readyLine === $Failed || ! StringQ[readyLine],
    Quiet@Check[KillProcess[process], Null];
    Return[$Failed]
  ];

  readyParts = StringSplit[readyLine, "\t"];
  If[Length[readyParts] < 3 || readyParts[[1]] =!= "READY",
    Quiet@Check[KillProcess[process], Null];
    Return[$Failed]
  ];

  startupSeconds = Quiet@Check[ToExpression[readyParts[[3]]], 0];
  <|
    "Process" -> process,
    "StartedNewQ" -> True,
    "StartupSeconds" -> startupSeconds
  |>
];


ClearAll[ResetJuliaSession];
ResetJuliaSession[] := Module[{},
  If[PersistentJuliaWorkerRunningQ[],
    Quiet@Check[WriteLine[$SUSYWBEPersistentJuliaWorker, "QUIT"], Null];
    Quiet@Check[KillProcess[$SUSYWBEPersistentJuliaWorker], Null]
  ];
  Quiet[Clear[$SUSYWBEPersistentJuliaWorker]];
  Quiet[Clear[$SUSYWBEPersistentJuliaWorkerKey]];
  Quiet[Clear[$SUSYWBEPersistentJuliaWorkerStartupSecondsPending]];
  Null
];


ClearAll[ConsumePersistentJuliaWorkerStartupSeconds];
ConsumePersistentJuliaWorkerStartupSeconds[] := Module[{startupSeconds},
  startupSeconds = Replace[
    Lookup[<|"Startup" -> If[ValueQ[$SUSYWBEPersistentJuliaWorkerStartupSecondsPending], $SUSYWBEPersistentJuliaWorkerStartupSecondsPending, 0]|>, "Startup", 0],
    Except[_?NumericQ] -> 0
  ];
  $SUSYWBEPersistentJuliaWorkerStartupSecondsPending = 0;
  startupSeconds
];


ClearAll[EnsurePersistentJuliaWorker];
EnsurePersistentJuliaWorker[] := Module[
  {
    runConfiguration, workerKey, workerInfo, fallbackConfiguration,
    backend
  },
  runConfiguration = GetJuliaRunConfiguration[];
  workerKey = PersistentJuliaWorkerKey[runConfiguration];

  If[
    PersistentJuliaWorkerRunningQ[] &&
    ValueQ[$SUSYWBEPersistentJuliaWorkerKey] &&
    $SUSYWBEPersistentJuliaWorkerKey === workerKey,
    Return[
      <|
        "Process" -> $SUSYWBEPersistentJuliaWorker,
        "StartedNewQ" -> False,
        "StartupSeconds" -> 0
      |>
    ]
  ];

  ResetJuliaSession[];
  backend = NormalizeJuliaBackend[Lookup[runConfiguration, "JuliaBackend", "ProcessPerRun"]];

  If[
    backend === "PersistentSessionSysimage" &&
    ! MatchQ[Lookup[runConfiguration, "JuliaSysimagePath", None], _String?FileExistsQ],
    runConfiguration = PlainJuliaRunConfiguration[runConfiguration];
    workerKey = PersistentJuliaWorkerKey[runConfiguration];
    $SUSYWBEJuliaRunConfiguration = runConfiguration
  ];

  workerInfo = StartPersistentJuliaWorker[runConfiguration];

  If[workerInfo === $Failed && backend === "PersistentSessionSysimage",
    fallbackConfiguration = PlainJuliaRunConfiguration[runConfiguration];
    workerInfo = StartPersistentJuliaWorker[fallbackConfiguration];
    If[workerInfo === $Failed,
      Return[$Failed]
    ];
    runConfiguration = fallbackConfiguration;
    workerKey = PersistentJuliaWorkerKey[runConfiguration];
    $SUSYWBEJuliaRunConfiguration = runConfiguration
  ];

  If[workerInfo === $Failed,
    Return[$Failed]
  ];

  $SUSYWBEPersistentJuliaWorker = workerInfo["Process"];
  $SUSYWBEPersistentJuliaWorkerKey = workerKey;
  $SUSYWBEPersistentJuliaWorkerStartupSecondsPending = workerInfo["StartupSeconds"];

  workerInfo
];


ClearAll[WarmupJuliaSession];
WarmupJuliaSession[] := Module[{runConfiguration},
  runConfiguration = GetJuliaRunConfiguration[];
  If[
    PersistentJuliaBackendQ[Lookup[runConfiguration, "JuliaBackend", "ProcessPerRun"]],
    EnsurePersistentJuliaWorker[],
    Null
  ]
];


ClearAll[ReadJuliaResultVector];
ReadJuliaResultVector[] := Module[
  {runConfiguration, resultFile, imported, values},
  runConfiguration = GetJuliaRunConfiguration[];
  resultFile = runConfiguration["OutputFile"];
  If[! FileExistsQ[resultFile],
    Return[$Failed]
  ];

  imported = Quiet@Check[Import[resultFile, "CSV"], $Failed];
  If[imported === $Failed || ! ListQ[imported] || Length[imported] < 2,
    Return[$Failed]
  ];

  values = imported[[2 ;;, 2]];
  If[! ListQ[values] || values === {},
    Return[$Failed]
  ];

  values = values /. value_String :> Quiet@Check[ToExpression[value], value];
  If[! VectorQ[values, NumericQ],
    Return[$Failed]
  ];

  N[values, prec]
];


ClearAll[ReadJuliaTimingFile];
ReadJuliaTimingFile[] := Module[
  {runConfiguration, timingFile, imported, rows},
  runConfiguration = GetJuliaRunConfiguration[];
  timingFile = Lookup[runConfiguration, "JuliaTimingFile", Missing["NotConfigured"]];
  If[! StringQ[timingFile] || ! FileExistsQ[timingFile],
    Return[<||>]
  ];

  imported = Quiet@Check[Import[timingFile, "CSV"], $Failed];
  If[imported === $Failed || ! ListQ[imported] || Length[imported] < 2,
    Return[<||>]
  ];

  rows = imported[[2 ;;]];
  Association @ Map[
    Function[{row},
      First[row] -> Quiet@Check[N[ToExpression[ToString[row[[2]], InputForm]], 20], row[[2]]]
    ],
    rows
  ]
];


ClearAll[WriteJuliaProcessLogs];
WriteJuliaProcessLogs[stdoutFile_, stderrFile_, processResult_] := Module[{},
  Export[stdoutFile, Lookup[processResult, "StandardOutput", ""], "String"];
  Export[stderrFile, Lookup[processResult, "StandardError", ""], "String"];
];


ClearAll[WaitForStableFile];
WaitForStableFile[path_String, timeout_?NumericQ, pollInterval_: 0.25] := Module[
  {deadline, previousSize = Missing["NotSeen"], stableCount = 0, currentSize},
  deadline = AbsoluteTime[] + timeout;
  While[AbsoluteTime[] <= deadline,
    If[FileExistsQ[path],
      currentSize = Quiet@Check[FileByteCount[path], 0];
      If[currentSize > 0,
        If[currentSize === previousSize,
          stableCount++;
          If[stableCount >= 2,
            Return[True]
          ],
          stableCount = 0;
          previousSize = currentSize
        ]
      ]
    ];
    Pause[pollInterval];
  ];
  False
];


ClearAll[BuildJuliaTimingAssociation];
BuildJuliaTimingAssociation[
  backend_String,
  runConfiguration_Association,
  baseTimings_Association,
  internalTimings_Association
] := Join[
  <|
    "Backend" -> backend,
    "StdoutFile" -> runConfiguration["StdoutFile"],
    "StderrFile" -> runConfiguration["StderrFile"],
    "TimingFile" -> runConfiguration["JuliaTimingFile"]
  |>,
  baseTimings,
  KeyMap["Julia/" <> # &, internalTimings]
];


ClearAll[RunJuliaViaPersistentSession];
RunJuliaViaPersistentSession[SYT_] := Module[
  {
    runConfiguration, outputFile, timingFile, warmupStart, warmupSeconds,
    evalStart, evalSeconds, juliaResult, importStart, importSeconds = 0,
    juliaOutput, internalTimings
  },
  runConfiguration = GetJuliaRunConfiguration[];
  outputFile = runConfiguration["OutputFile"];
  timingFile = runConfiguration["JuliaTimingFile"];

  If[FileExistsQ[outputFile],
    Quiet@DeleteFile[outputFile]
  ];
  If[FileExistsQ[timingFile],
    Quiet@DeleteFile[timingFile]
  ];

  warmupStart = AbsoluteTime[];
  WarmupJuliaSession[];
  warmupSeconds = AbsoluteTime[] - warmupStart;

  evalStart = AbsoluteTime[];
  juliaResult = Quiet @ Check[
    SetPrecision[ExternalEvaluate[EnsureJuliaSession[], juliaInputNew[SYT, \[CapitalLambda]0Interim]], prec],
    $Failed
  ];
  evalSeconds = AbsoluteTime[] - evalStart;

  If[ListQ[juliaResult] && VectorQ[juliaResult, NumericQ],
    juliaOutput = juliaResult,
    importStart = AbsoluteTime[];
    juliaOutput = ReadJuliaResultVector[];
    importSeconds = AbsoluteTime[] - importStart
  ];

  internalTimings = ReadJuliaTimingFile[];
  <|
    "Vector" -> juliaOutput,
    "Timings" -> BuildJuliaTimingAssociation[
      "PersistentSession",
      runConfiguration,
      <|
        "WarmupSeconds" -> warmupSeconds,
        "EvaluationSeconds" -> evalSeconds,
        "ImportSeconds" -> importSeconds,
        "TotalBackendSeconds" -> warmupSeconds + evalSeconds + importSeconds
      |>,
      internalTimings
    ]
  |>
];


ClearAll[RunJuliaViaExternalSession];
RunJuliaViaExternalSession[SYT_] := RunJuliaViaPersistentSession[SYT];


ClearAll[RunJuliaViaCLI];
RunJuliaViaCLI[SYT_] := Module[
  {
    runConfiguration, runnerPath, outputFile, stdoutFile, stderrFile,
    timingFile, juliaTimeout, processStart, processSeconds,
    waitStart, waitSeconds, importStart, importSeconds, juliaProcessFlags,
    juliaCommand, juliaRunResult, juliaOutput, internalTimings
  },
  runConfiguration = GetJuliaRunConfiguration[];
  runnerPath = FileNameJoin[{SUSYWBEJuliaDirectory[], "SUSYWBEJuliaTaskRunner.jl"}];
  outputFile = runConfiguration["OutputFile"];
  stdoutFile = runConfiguration["StdoutFile"];
  stderrFile = runConfiguration["StderrFile"];
  timingFile = runConfiguration["JuliaTimingFile"];
  juliaTimeout = Lookup[runConfiguration, "JuliaTimeout", 900];
  juliaProcessFlags = Lookup[runConfiguration, "JuliaProcessFlags", {"--threads=1"}];

  If[FileExistsQ[outputFile],
    Quiet@DeleteFile[outputFile]
  ];
  If[FileExistsQ[timingFile],
    Quiet@DeleteFile[timingFile]
  ];

  juliaCommand = Join[
    {"julia"},
    Replace[juliaProcessFlags, Except[_List] :> {"--threads=1"}],
    {
      "--project=" <> SUSYWBEPackageDirectory[],
      runnerPath,
      runConfiguration["SavedDataDir"],
      runConfiguration["InitialDataFile"],
      outputFile,
      timingFile
    }
  ];

  processStart = AbsoluteTime[];
  juliaRunResult = Quiet @ Check[
    TimeConstrained[RunProcess[juliaCommand, All], juliaTimeout, $Aborted],
    $Failed
  ];
  processSeconds = AbsoluteTime[] - processStart;

  If[juliaRunResult === $Aborted,
    Export[stdoutFile, "", "String"];
    Export[
      stderrFile,
      "Julia subprocess exceeded timeout of " <> ToString[juliaTimeout] <> " seconds.",
      "String"
    ];
    Return[$Failed]
  ];

  If[AssociationQ[juliaRunResult],
    WriteJuliaProcessLogs[stdoutFile, stderrFile, juliaRunResult]
  ];

  If[
    juliaRunResult === $Failed ||
    Lookup[juliaRunResult, "ExitCode", 1] =!= 0,
    Return[$Failed]
  ];

  waitStart = AbsoluteTime[];
  If[! WaitForStableFile[outputFile, Min[30, juliaTimeout]],
    Return[$Failed]
  ];
  waitSeconds = AbsoluteTime[] - waitStart;

  importStart = AbsoluteTime[];
  juliaOutput = ReadJuliaResultVector[];
  importSeconds = AbsoluteTime[] - importStart;
  If[!(ListQ[juliaOutput] && VectorQ[juliaOutput, NumericQ]),
    Return[$Failed]
  ];

  internalTimings = ReadJuliaTimingFile[];
  <|
    "Vector" -> juliaOutput,
    "Timings" -> BuildJuliaTimingAssociation[
      "CLI",
      runConfiguration,
      <|
        "ProcessSeconds" -> processSeconds,
        "WaitForOutputSeconds" -> waitSeconds,
        "ImportSeconds" -> importSeconds,
        "StartupAndProcessOverheadSeconds" -> Max[
          0,
          processSeconds - Lookup[internalTimings, "script_total_seconds", 0]
        ],
        "TotalBackendSeconds" -> processSeconds + importSeconds
      |>,
      internalTimings
    ]
  |>
];


ClearAll[RunJuliaViaPersistentSession];
RunJuliaViaPersistentSession[SYT_] := Module[
  {
    runConfiguration, workerInfo, process, outputFile, timingFile, stdoutFile,
    stderrFile, juliaTimeout, startupSeconds, commandString, responseLine,
    responseParts, roundTripStart, roundTripSeconds, waitStart, waitSeconds,
    importStart, importSeconds, juliaOutput, internalTimings, backendLabel
  },
  runConfiguration = GetJuliaRunConfiguration[];
  outputFile = runConfiguration["OutputFile"];
  timingFile = runConfiguration["JuliaTimingFile"];
  stdoutFile = runConfiguration["StdoutFile"];
  stderrFile = runConfiguration["StderrFile"];
  juliaTimeout = Lookup[runConfiguration, "JuliaTimeout", 900];

  workerInfo = EnsurePersistentJuliaWorker[];
  If[workerInfo === $Failed,
    Return[$Failed]
  ];
  runConfiguration = GetJuliaRunConfiguration[];
  backendLabel = NormalizeJuliaBackend[Lookup[runConfiguration, "JuliaBackend", "PersistentSession"]];
  process = workerInfo["Process"];
  startupSeconds = ConsumePersistentJuliaWorkerStartupSeconds[];

  commandString = StringRiffle[
    {
      "RUN",
      runConfiguration["SavedDataDir"],
      runConfiguration["InitialDataFile"],
      outputFile,
      timingFile,
      stdoutFile,
      stderrFile,
      ToString[N[startupSeconds, 20], InputForm]
    },
    "\t"
  ];

  roundTripStart = AbsoluteTime[];
  Quiet@Check[WriteLine[process, commandString], $Failed];
  responseLine = ReadJuliaWorkerLine[process, juliaTimeout];
  roundTripSeconds = AbsoluteTime[] - roundTripStart;

  If[
    responseLine === $Aborted ||
    responseLine === $Failed ||
    ! StringQ[responseLine],
    Return[$Failed]
  ];

  responseParts = StringSplit[responseLine, "\t"];
  If[
    Length[responseParts] < 2 ||
    responseParts[[1]] =!= "RESULT" ||
    responseParts[[2]] =!= "OK",
    Return[$Failed]
  ];

  waitStart = AbsoluteTime[];
  If[! WaitForStableFile[outputFile, Min[30, juliaTimeout]],
    Return[$Failed]
  ];
  waitSeconds = AbsoluteTime[] - waitStart;

  importStart = AbsoluteTime[];
  juliaOutput = ReadJuliaResultVector[];
  importSeconds = AbsoluteTime[] - importStart;
  If[!(ListQ[juliaOutput] && VectorQ[juliaOutput, NumericQ]),
    Return[$Failed]
  ];

  internalTimings = ReadJuliaTimingFile[];
  <|
    "Vector" -> juliaOutput,
    "Timings" -> BuildJuliaTimingAssociation[
      backendLabel,
      runConfiguration,
      <|
        "SessionStartupSeconds" -> startupSeconds,
        "RoundTripSeconds" -> roundTripSeconds,
        "WaitForOutputSeconds" -> waitSeconds,
        "ImportSeconds" -> importSeconds,
        "TotalBackendSeconds" -> startupSeconds + roundTripSeconds + importSeconds
      |>,
      internalTimings
    ]
  |>
];


ClearAll[RunJuliaViaExternalSession];
RunJuliaViaExternalSession[SYT_] := RunJuliaViaPersistentSession[SYT];


ClearAll[RunJuliaViaProcessPerRun];
RunJuliaViaProcessPerRun[SYT_] := Module[
  {
    runConfiguration, runnerPath, outputFile, stdoutFile, stderrFile,
    timingFile, juliaTimeout, processStart, processSeconds,
    waitStart, waitSeconds, importStart, importSeconds,
    juliaCommand, juliaRunResult, juliaOutput, internalTimings
  },
  runConfiguration = GetJuliaRunConfiguration[];
  runnerPath = FileNameJoin[{SUSYWBEJuliaDirectory[], "SUSYWBEJuliaTaskRunner.jl"}];
  outputFile = runConfiguration["OutputFile"];
  stdoutFile = runConfiguration["StdoutFile"];
  stderrFile = runConfiguration["StderrFile"];
  timingFile = runConfiguration["JuliaTimingFile"];
  juliaTimeout = Lookup[runConfiguration, "JuliaTimeout", 900];

  If[FileExistsQ[outputFile],
    Quiet@DeleteFile[outputFile]
  ];
  If[FileExistsQ[timingFile],
    Quiet@DeleteFile[timingFile]
  ];

  juliaCommand = Join[
    BuildJuliaCommand[runnerPath, runConfiguration],
    {
      runConfiguration["SavedDataDir"],
      runConfiguration["InitialDataFile"],
      outputFile,
      timingFile
    }
  ];

  processStart = AbsoluteTime[];
  juliaRunResult = Quiet @ Check[
    TimeConstrained[RunProcess[juliaCommand, All], juliaTimeout, $Aborted],
    $Failed
  ];
  processSeconds = AbsoluteTime[] - processStart;

  If[juliaRunResult === $Aborted,
    Export[stdoutFile, "", "String"];
    Export[
      stderrFile,
      "Julia subprocess exceeded timeout of " <> ToString[juliaTimeout] <> " seconds.",
      "String"
    ];
    Return[$Failed]
  ];

  If[AssociationQ[juliaRunResult],
    WriteJuliaProcessLogs[stdoutFile, stderrFile, juliaRunResult]
  ];

  If[
    juliaRunResult === $Failed ||
    Lookup[juliaRunResult, "ExitCode", 1] =!= 0,
    Return[$Failed]
  ];

  waitStart = AbsoluteTime[];
  If[! WaitForStableFile[outputFile, Min[30, juliaTimeout]],
    Return[$Failed]
  ];
  waitSeconds = AbsoluteTime[] - waitStart;

  importStart = AbsoluteTime[];
  juliaOutput = ReadJuliaResultVector[];
  importSeconds = AbsoluteTime[] - importStart;
  If[!(ListQ[juliaOutput] && VectorQ[juliaOutput, NumericQ]),
    Return[$Failed]
  ];

  internalTimings = ReadJuliaTimingFile[];
  <|
    "Vector" -> juliaOutput,
    "Timings" -> BuildJuliaTimingAssociation[
      "ProcessPerRun",
      runConfiguration,
      <|
        "ProcessSeconds" -> processSeconds,
        "WaitForOutputSeconds" -> waitSeconds,
        "ImportSeconds" -> importSeconds,
        "StartupAndProcessOverheadSeconds" -> Max[
          0,
          processSeconds - Lookup[internalTimings, "script_total_seconds", 0]
        ],
        "TotalBackendSeconds" -> processSeconds + importSeconds
      |>,
      internalTimings
    ]
  |>
];


ClearAll[RunJuliaViaCLI];
RunJuliaViaCLI[SYT_] := RunJuliaViaProcessPerRun[SYT];


IterateUptdInterimJulia[SYT_]:=Block[{},
 runConfiguration = GetJuliaRunConfiguration[];
 exportSeconds = First@AbsoluteTiming[exportToJuliaInitialData[SYT]];
 SUSYWBEProgressPrint["Initial norm: ",Norm[InterpEqnsUptd[\[CapitalLambda]0]/.sol[\[CapitalLambda]0]]];
 SUSYWBEProgressPrint["First findroot norm: ",Norm[(InterpEqnsUptd[\[CapitalLambda]0]// ExpandAll)/.MYminsolrep]];

 backendResult = Switch[
  NormalizeJuliaBackend[Lookup[runConfiguration, "JuliaBackend", "ProcessPerRun"]],
  "ProcessPerRun",
  RunJuliaViaProcessPerRun[SYT],
  "PersistentSession",
  RunJuliaViaPersistentSession[SYT],
  "PersistentSessionSysimage",
  RunJuliaViaPersistentSession[SYT],
  _,
  RunJuliaViaProcessPerRun[SYT]
 ];

 If[AssociationQ[backendResult],
  AppendTo[
   savedJuliaTime,
   Join[
    <|
      "TableauStep" -> SYT,
      "ExportSeconds" -> exportSeconds
    |>,
    Lookup[backendResult, "Timings", <||>]
   ]
  ]
 ];

 juliaOutput = If[AssociationQ[backendResult], Lookup[backendResult, "Vector", $Failed], $Failed];

If[!(ListQ[juliaOutput] && VectorQ[juliaOutput, NumericQ]),
  Throw[Nothing, "BadJuliaOutput"];
];


 minsolrep=Rule@@@Transpose[{susyvars,SetPrecision[juliaOutput,prec]}];
 sol[0]=minsolrep;
 AppendTo[\[CapitalLambda]vals,0];
(* juliaTime = ExternalEvaluate[sessionJulia,"[time_dummy,time_final]"];
 AppendTo[savedJuliaTime,juliaTime];*)
]


ClearAll[AppendWorkflowStageTiming];
AppendWorkflowStageTiming[stage_Association] := If[
  ValueQ[savedWorkflowStageTime] && ListQ[savedWorkflowStageTime],
  AppendTo[savedWorkflowStageTime, stage]
];


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
    \[Lambda]Tstart, \[Lambda]start, generateQsystemSeconds,
    generateSUSYWsystemSeconds, largeLambdaExpansionSeconds,
    generateAsymptoticSolutionsSeconds, iteratorSeconds,
    finalizeSolutionSeconds, totalStageSeconds
  },
  
  (* Solve the initial YT \[LongDash] one row with increasing tableau values and one box in the next row *)
  Steps = {};
  
  \[Lambda]Tstart = SYT;
  \[Lambda]start = \[Lambda]Tstart // ToYD;
  
  generateQsystemSeconds = First@AbsoluteTiming[GenerateQsystem[\[Lambda]start]];
  generateSUSYWsystemSeconds = First@AbsoluteTiming[GenerateSUSYWsystem[\[Lambda]start]];
  largeLambdaExpansionSeconds = First@AbsoluteTiming[Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]Tstart]];
  generateAsymptoticSolutionsSeconds = First@AbsoluteTiming[GenerateSolsFromAsymptoticsUptdStart[\[Lambda]start]];
  
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  
  iteratorSeconds = First@AbsoluteTiming[IterateUptdStart[\[Lambda]Tstart]];
  
  finalizeSolutionSeconds = First@AbsoluteTiming[
    currentsol = {
      \[CapitalLambda]vals,
      sol[\[CapitalLambda]vals[[#]]] & /@ Range[1, Length[\[CapitalLambda]vals]],
      Ccoeff
    }
  ];
  totalStageSeconds =
    generateQsystemSeconds +
    generateSUSYWsystemSeconds +
    largeLambdaExpansionSeconds +
    generateAsymptoticSolutionsSeconds +
    iteratorSeconds +
    finalizeSolutionSeconds;
  AppendWorkflowStageTiming[<|
    "Stage" -> "Start",
    "Tableau" -> \[Lambda]Tstart,
    "YoungDiagram" -> \[Lambda]start,
    "GenerateQsystemSeconds" -> generateQsystemSeconds,
    "GenerateSUSYWsystemSeconds" -> generateSUSYWsystemSeconds,
    "LargeLambdaExpansionSeconds" -> largeLambdaExpansionSeconds,
    "GenerateAsymptoticSolutionsSeconds" -> generateAsymptoticSolutionsSeconds,
    "IteratorSeconds" -> iteratorSeconds,
    "FinalizeSolutionSeconds" -> finalizeSolutionSeconds,
    "TotalStageSeconds" -> totalStageSeconds,
    "WorkflowTimingMeasuredQ" -> True
  |>];
  currentsol
]




(* ::Subsection:: *)
(*SolutionFromSYTUptdInterim*)


SolutionFromSYTUptdInterim[SYTcurrent_, SYTlast_, solnlast_] := Block[{
    \[Lambda]Tcurrent, \[Lambda]Tlast, \[Lambda]current, \[Lambda]last,
    generateQsystemSeconds, generateSUSYWsystemSeconds,
    largeLambdaExpansionSeconds, generateAsymptoticSolutionsSeconds,
    iteratorSeconds, finalizeSolutionSeconds, totalStageSeconds
  },
  
  Steps = {};
  
  \[Lambda]Tcurrent = SYTcurrent;
  \[Lambda]Tlast = SYTlast;
  
  \[Lambda]current = \[Lambda]Tcurrent // ToYD;
  \[Lambda]last = \[Lambda]Tlast // ToYD;
  
  generateQsystemSeconds = First@AbsoluteTiming[GenerateQsystem[\[Lambda]current]];
  generateSUSYWsystemSeconds = First@AbsoluteTiming[GenerateSUSYWsystem[\[Lambda]current]];
  largeLambdaExpansionSeconds = First@AbsoluteTiming[Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent, \[Lambda]Tlast, solnlast]];
  generateAsymptoticSolutionsSeconds = First@AbsoluteTiming[GenerateSolsFromAsymptoticsUptdInterim[\[Lambda]current, \[Lambda]last, solnlast]];
  
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  
  
  SUSYWBEProgressPrint["startJulia: ", SYTcurrent];
  (*IterateUptdInterim[\[Lambda]Tcurrent];*)
  iteratorSeconds = First@AbsoluteTiming[$CurrentIterator[\[Lambda]Tcurrent]];
  

  
  finalizeSolutionSeconds = First@AbsoluteTiming[
    currentsol = {
      \[CapitalLambda]vals,
      sol[\[CapitalLambda]vals[[#]]] & /@ Range[1, Length[\[CapitalLambda]vals]],
      Ccoeff
    }
  ];
  totalStageSeconds =
    generateQsystemSeconds +
    generateSUSYWsystemSeconds +
    largeLambdaExpansionSeconds +
    generateAsymptoticSolutionsSeconds +
    iteratorSeconds +
    finalizeSolutionSeconds;
  AppendWorkflowStageTiming[<|
    "Stage" -> "Interim",
    "Tableau" -> \[Lambda]Tcurrent,
    "PreviousTableau" -> \[Lambda]Tlast,
    "YoungDiagram" -> \[Lambda]current,
    "PreviousYoungDiagram" -> \[Lambda]last,
    "GenerateQsystemSeconds" -> generateQsystemSeconds,
    "GenerateSUSYWsystemSeconds" -> generateSUSYWsystemSeconds,
    "LargeLambdaExpansionSeconds" -> largeLambdaExpansionSeconds,
    "GenerateAsymptoticSolutionsSeconds" -> generateAsymptoticSolutionsSeconds,
    "IteratorSeconds" -> iteratorSeconds,
    "FinalizeSolutionSeconds" -> finalizeSolutionSeconds,
    "TotalStageSeconds" -> totalStageSeconds,
    "WorkflowTimingMeasuredQ" -> True
  |>];
  currentsol
]


(* ::Subsection::Closed:: *)
(*SolutionFromSYTUptdStepwiseWronskian*)


SolutionFromSYTUptdStepwiseWronskian[SYT_] := Catch[
  Block[{ \[Lambda]Tlist, buildTableauSequenceSeconds },
    StepsStepwise = {};
    ansWholeIteration = {};
    predictorCorrectorList = {};
    
    buildTableauSequenceSeconds = First@AbsoluteTiming[
      \[Lambda]Tlist = Table[
        Select[MemberQ[Range[1, i], #] &] /@ SYT /. {{} -> Nothing},
        {i, Count[SYT[[1]] - Range[Length[SYT[[1]]]], 0], Max[SYT]}
      ][[2 ;;]];
    ];
    AppendWorkflowStageTiming[<|
      "Stage" -> "BuildTableauSequence",
      "Tableau" -> SYT,
      "YoungDiagram" -> ToYD[SYT],
      "NumberOfTableaux" -> Length[\[Lambda]Tlist],
      "BuildTableauSequenceSeconds" -> buildTableauSequenceSeconds,
      "WorkflowTimingMeasuredQ" -> True
    |>];
    
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
