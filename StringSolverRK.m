(* ::Package:: *)

<<"/home/zuxian/Documents/BAE/functions.m"


(* ::Subsubsection:: *)
(*Initial equations*)


(*Some initial definitions.*)

log[z_,branch_:0,branchcut_:-Pi]:=Log[Abs[z]]+I*(Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi+2Pi*branch); 
arg[z_,branch_:0,branchcut_:-Pi]:=Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi;
F[u_,branch_:0,branchcut_:-Pi]:=(-1/(2Pi*I))log[(u+I)/(u-I),branch,branchcut];
Fsym[u_,branch_:0,branchcut_:-Pi]:=F[u,branch,branchcut]-1/2;
Fsym[u_,-1,0]:=(1/Pi)ArcTan[u];


(* ::Subsubsection:: *)
(*ModesConfiguration*)


(*in notation (a,s,k)*)
ModesConfigRandom[yd_] := Module[{},
  AM        = AdmissibleModes[yd] // Transpose;
  AMChoice  = RandomChoice[AM];
  Modes     = AMChoice[[1]];
  Mmatrices = AMChoice[[2]];

  Table[
    Table[
      RandomSample[
        Range[-Modes[[j, k]], Modes[[j, k]]],
        Mmatrices[[j, k]] // Total
      ],
      {k, Length[Modes[[j]]]}
    ],
    {j, Length[Modes]}
  ]
]


ModesConfigAllCombos[yd_] := Module[{AM, build},
  AM = AdmissibleModes[yd] // Transpose;  (* list of {Modes, Mmatrices} choices *)

  build[{Modes_, Mmatrices_}] := Module[{optsByJ, rowsByJ},
    (* For each (j,k), all size-s subsets from -m..m *)
    optsByJ = Table[
      Table[
        With[{m = Modes[[j, k]], s = Total[Mmatrices[[j, k]]]},
          Subsets[Range[-m, m], {s}]      (* includes {{}} when s == 0 *)
        ],
        {k, Length[Modes[[j]]]}
      ],
      {j, Length[Modes]}
    ];

    rowsByJ = Tuples /@ optsByJ;          (* for each j: combine across k *)
    Tuples[rowsByJ]                       (* combine across j *)
  ];

  Flatten[build /@ AM, 1]                 (* all choices in AM *)
]



(* Randomly sample n configurations total, across all AM choices *)
ModesConfigRandomCombos[yd_, n_: 30, seed_: Automatic] := Module[
  {AM, sampleOnePair},
  If[seed =!= Automatic, SeedRandom[seed]];
  AM = AdmissibleModes[yd] // Transpose;  (* list of {Modes, Mmatrices} *)

  sampleOnePair[{Modes_, Mmatrices_}] := Table[
    With[{m = Modes[[j, k]], s = Total[Mmatrices[[j, k]]]},
      If[s == 0, {}, Sort @ RandomSample[Range[-m, m], s]]
    ],
    {j, Length[Modes]}, {k, Length[Modes[[j]]]}
  ];

  Table[
    sampleOnePair @ RandomChoice[AM],
    {n}
  ]
]



(* Randomly sample n UNIQUE configurations across all AM choices *)
ModesConfigRandomUnique[yd_, n_: 1, seed_: Automatic, maxTriesMultiplier_: 50] := Module[
  {AM, sampleOnePair, countForPair, totalSpace, target, bag, out, tries = 0, cfg},
  
  If[seed =!= Automatic, SeedRandom[seed]];
  AM = AdmissibleModes[yd] // Transpose;  (* list of {Modes, Mmatrices} *)

  (* number of combinations for a given {Modes, Mmatrices} *)
  countForPair[{Modes_, Mmatrices_}] := Times @@ Flatten @ Table[
      With[{m = Modes[[j, k]], s = Total[Mmatrices[[j, k]]]},
        Binomial[2 m + 1, s]
      ],
      {j, Length[Modes]}, {k, Length[Modes[[j]]]}
    ];

  totalSpace = Total[countForPair /@ AM];
  target = Min[n, totalSpace];

  sampleOnePair[{Modes_, Mmatrices_}] := Table[
    With[{m = Modes[[j, k]], s = Total[Mmatrices[[j, k]]]},
      If[s == 0, {}, Sort @ RandomSample[Range[-m, m], s]]
    ],
    {j, Length[Modes]}, {k, Length[Modes[[j]]]}
  ];

  bag = <||>;    (* set of seen configurations *)
  out = {};      

  While[Length[out] < target && tries < maxTriesMultiplier target,
    tries++;
    cfg = sampleOnePair @ RandomChoice[AM];
    If[!KeyExistsQ[bag, cfg],
      bag[cfg] = True;
      AppendTo[out, cfg];
    ];
  ];

  If[Length[out] < target && target < n,
    MessageDialog@Row[{
      "Only ", Length[out], " unique configurations available (",
      totalSpace, " total in space); returned all unique ones."
    }]
  ];

  out
]



(*Admissible string configurations for a YD; that is, the configs such that N_as is non-zero for all entries.*)
AdmissibleStringConfig[yd_]:=Module[{Mmatrices},
Mmatrices=Msetmatrix[yd];
Table[Module[{Holes},Holes=Delete[-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[Length[Mmatrix[[1]]]],{{1},{-1}}];
If[AllTrue[Holes//Flatten,GreaterEqualThan[0]],Mmatrix,Nothing]],{Mmatrix,Mmatrices}]]

(*For a specific set of strings for a YD (eg {{2,1},{1},{}} as in rig {{{1,1,1,1,1,1,1}},{{2,1},{1},{}},X} for YD={4,2,1}), we produce all possible X and return a list of all possible rigs.*)
RigsForStringConfig[yd_,string_]:=Block[{},
stringmatrix=Table[Count[string[[i]],j],{i,Length[string]-1},{j,Max[string//Flatten]}];
holes=Delete[-Cartan[Length[#]] . # . Kernel[Length[#[[1]]]],{{1},{-1}}]&@(Append[Prepend[stringmatrix,SparseArray[1->(AugmentedYoungD[yd]//First//First),Length[stringmatrix[[1]]]]],ConstantArray[0,Length[stringmatrix[[1]]]]]);
{{ConstantArray[1,Total[yd]]},string,#}&/@Tuples[Tuples/@Table[Range[0,holes[[i,string[[i,j]]]]],{i,Length[string]},{j,Length[string[[i]]]}]]]


(*Convert a list of strings of form {v[a,s,k]->x,...} where a is the (a+1,0) coordinate, s is the length of the string and k is the number of the string of this type into a list of roots {{x1,x2,...},{...}} where each nested list is a (a,0) coordinate*)
Strings2Roots[strings_]:=-Flatten/@Map[Table[#[[2]]-I/2*(#[[1,2]]-1-2k),{k,0,#[[1,2]]-1}]&,GatherBy[strings,#[[1,1]]&],{2}]


(* ::Subsubsection:: *)
(*Equation system for a given mode configuration. To solve.*)


GenerateSystem[modes_,L_]:=(
BAElog[k_, a_, s_, modeconfig_] := 
  modeconfig[[a, s, k]] 
  - \[Epsilon] * 
    Sum[
      Sum[
        If[{sss, jjj} != {s, k},
          If[s != sss,
            Fsym[2 (v[a, s, k] - v[a, sss, jjj])/(s - sss), -1, 0],
            0
          ]
          + Fsym[2 (v[a, s, k] - v[a, sss, jjj])/(s + sss), -1, 0]
          + 2 Sum[
              If[nnn != 0,
                Fsym[(v[a, s, k] - v[a, sss, jjj])/nnn, -1, 0],
                0
              ],
              {nnn, (s - sss)/2 + 1, (s + sss)/2 - 1}
            ],
          0
        ],
        {jjj, 1, Length[modes[[a, sss]]]}
      ],
      {sss, 1, Length[modes[[1]]]}
    ]
  + If[
      a == 1,
      L * Fsym[2*v[a, s, k]/s, -1, 0],
      Sum[
        Sum[
          Sum[
            If[nn != 0,
              Fsym[(v[a, s, k] - v[a - 1, ss, jj])/nn, -1, 0],
              0
            ],
            {nn, (s - ss)/2 + 1/2, (s + ss)/2 - 1/2}
          ],
          {jj, 1, Length[modes[[a - 1, ss]]]}
        ],
        {ss, 1, Length[modes[[1]]]}
      ]
    ]
  + \[Epsilon] * 
    If[
      a == Length[modes],
      0,
      Sum[
        Sum[
          Sum[
            If[nnnn != 0,
              Fsym[(v[a, s, k] - v[a + 1, ssss, jjjj])/nnnn, -1, 0],
              0
            ],
            {nnnn, (s - ssss)/2 + 1/2, (s + ssss)/2 - 1/2}
          ],
          {jjjj, 1, Length[modes[[a + 1, ssss]]]}
        ],
        {ssss, 1, Length[modes[[1]]]}
      ]
    ]
;
Allrels = 
  Table[
    BAElog[k, a, s, modes],
    {a, 1, Length[modes]},                (* nesting level index *)
    {s, 1, Length[modes[[1]]]},           (* string length index *)
    {k, 1, Length[modes[[a, s]]]}         (* root index within that string *)
  ] // Flatten;

vars = 
  Table[
    v[a, s, k],
    {a, 1, Length[modes]},                (* nesting level index *)
    {s, 1, Length[modes[[1]]]},           (* string length index *)
    {k, 1, Length[modes[[a, s]]]}         (* root index within that string *)
  ] // Flatten;


J=D[Allrels,{vars}];
H=D[#,{vars,2}]&/@Allrels;
dddf=D[#,{vars,3}]&/@Allrels;
fdot=D[Allrels,\[Epsilon]];
dfdot=D[fdot,{vars}];
ddfdot=D[#,{vars,2}]&/@fdot;
)


(* ::Subsubsection:: *)
(*Asymptotic initial conditions*)


Small\[Epsilon]Expansion[modes_, L_] := Module[{a},

  (* Seed from first block *)
  startpredictor = {
    Table[
      ss/2 * Tan[-modes[[1, ss, kk]] Pi/L],
      {ss, Length[modes[[1]]]},
      {kk, Length[modes[[1, ss]]]}
    ] // Flatten
  };

  (* Build successive predictors *)
  While[Length[startpredictor] < Length[modes],
    a = Length[startpredictor] + 1;

    AppendTo[
      startpredictor,
      FindRoot[
        (
          Table[
            modes[[a, s, k]] ==
              -Sum[
                 Sum[
                   Sum[
                     If[nn != 0,
                       Fsym[(v[a, s, k] - v[a - 1, ss, jj])/nn, -1, 0],
                       0
                     ],
                     {nn, (s - ss)/2 + 1/2, (s + ss)/2 - 1/2}
                   ],
                   {jj, 1, Length[modes[[a - 1, ss]]]}
                 ],
                 {ss, 1, Length[modes[[1]]]}
               ],
            {s, 1, Length[modes[[1]]]},
            {k, 1, Length[modes[[a, s]]]}
          ] // Flatten
        ) /. Thread[
          Rule[
            Table[
              v[a - 1, ss, jj],
              {ss, 1, Length[modes[[1]]]},
              {jj, 1, Length[modes[[a - 1, ss]]]}
            ] // Flatten,
            startpredictor[[a - 1]]
          ]
        ],
        {
          Table[v[a, s, k], {s, 1, Length[modes[[1]]]}, {k, 1, Length[modes[[a, s]]]}] // Flatten,
          Table[0, {s, 1, Length[modes[[1]]]}, {k, 1, Length[modes[[a, s]]]}] // Flatten
        } // Transpose,
        WorkingPrecision -> prec,
        PrecisionGoal   -> prec,
        AccuracyGoal    -> prec/2,
        MaxIterations   -> \[Infinity]
      ] // Values
    ];
  ];
  startpredictorRandom = 
  startpredictor + RandomReal[{-0.001, 0.001}, Dimensions[startpredictor]];

  (* Final substitution *)
  startvalue = Thread[vars -> (startpredictorRandom // Flatten)]
]



(* ::Subsubsection:: *)
(*Corrector*)


stringfinder[ \[Epsilon]0_, predictor_ ] := (
  minsolrep = FindRoot[
    Allrels /. \[Epsilon] -> \[Epsilon]0,
    {vars, vars /. predictor} // Transpose,
    WorkingPrecision -> prec,
    PrecisionGoal   -> prec,
    AccuracyGoal    -> prec/2,
    MaxIterations   -> \[Infinity]
  ];
);

stringfinderThrow[ \[Epsilon]0_, predictor_ ] := Block[ {},
  i = 0;
  minsolrep = FindRoot[
    Allrels /. \[Epsilon] -> \[Epsilon]0,
    {vars, vars /. predictor} // Transpose,
    WorkingPrecision -> prec,
    PrecisionGoal   -> prec,
    AccuracyGoal    -> prec/2,
    MaxIterations   -> \[Infinity],
    EvaluationMonitor :> (
      i++;
      If[ i > MyMaxIterations, Throw["Too big step"] ]
    )
  ];
];


(*Approximate zero*)
stringfinderThrow[\[Epsilon]0_, predictor_] := Block[{},
  
  Steps = {};  (* record evolution of vars during FindRoot *)

  minsolrep = 
    FindRoot[
      Allrels /. \[Epsilon] -> \[Epsilon]0,
      {vars, vars /. predictor} // Transpose,
      WorkingPrecision -> prec,
      PrecisionGoal   -> prec,
      AccuracyGoal    -> prec/2,
      MaxIterations   -> \[Infinity],
      
      EvaluationMonitor :> (
        AppendTo[Steps, vars];
        
        If[
          Length[Steps] > 2 &&
          Norm[Steps[[-2]] - Steps[[-3]]] != 0 &&
          Norm[Steps[[-1]] - Steps[[-2]]] / 
            Norm[Steps[[-2]] - Steps[[-3]]] > (1/2)^(2^(Length[Steps[[;; -3]]] - 1)),
          
          Throw["Too big step"]
        ]
      )
    ];
];


(* ::Subsubsection:: *)
(*Predictor*)


stringpred2[solLast_,\[Epsilon]Last_,d\[Epsilon]_]:=solLast

(*interpolation*)
stringpred2[solLast_,\[Epsilon]Last_,d\[Epsilon]_]:=(minterpord=Min[Length[\[Epsilon]vals]-1,interpord];Thread[Rule[vars,Sum[(vars/.sol[\[Epsilon]vals[[-j]]])Product[If[j==j2,1,(\[Epsilon]Last+d\[Epsilon]-\[Epsilon]vals[[-j2]])/(\[Epsilon]vals[[-j]]-\[Epsilon]vals[[-j2]])],{j2,minterpord}],{j,minterpord}]]]);

(*Linear approximation*)
stringpred2[solLast_,\[Epsilon]Last_,d\[Epsilon]_]:=Thread[(solLast//Keys)->(solLast//Values)+(LinearSolve[J/.solLast/.\[Epsilon]->\[Epsilon]Last,-fdot/.solLast/.\[Epsilon]->\[Epsilon]Last])*d\[Epsilon]];


(*Pad\[EAcute] approximation*)
stringpred[sol_,\[Epsilon]Last_,d\[Epsilon]_]:=
(
ordI=LinearSolve[J/.sol/.\[Epsilon]->\[Epsilon]Last,-fdot/.sol];
ordII=LinearSolve[J/.sol/.\[Epsilon]->\[Epsilon]Last,-(1/2 (ordI . (#) . ordI&/@(H/.sol/.\[Epsilon]->\[Epsilon]Last))+(dfdot/.sol) . ordI)];
ordIII=LinearSolve[J/.sol/.\[Epsilon]->\[Epsilon]Last,-(ordI . (#) . ordII&/@(H/.sol/.\[Epsilon]->\[Epsilon]Last)+(dfdot/.sol) . ordII+1/2 ((ordI . (#) . ordI)&/@(ddfdot/.sol))+1/6 ((#) . ordI . ordI . ordI&/@(dddf/.sol/.\[Epsilon]->\[Epsilon]Last)))];
Table[Thread[(sol[[i]]//Keys)->(sol[[i]]//Values)+(ordI[[i]])*d\[Epsilon]+If[ordII[[i]]==0,0,ordII[[i]]*d\[Epsilon]^2/(1-d\[Epsilon]*ordIII[[i]]/ordII[[i]])]],{i,Length[sol]}]
)



(* --- Runge\[Dash]Kutta (classical RK4) predictor --- *)
stringpredRK4[solLast_, \[Epsilon]Last_, d\[Epsilon]_] := Module[
  {f, add, k1, k2, k3, k4, s12, s3, keys, vals},
  
  (* helper: vector field dv/d\[CurlyEpsilon] = -J^{-1} fdot, evaluated at (\[CurlyEpsilon], sol) *)
  f[sol_, \[CurlyEpsilon]_] := LinearSolve[
    J /. sol /. \[Epsilon] -> \[CurlyEpsilon],
    - (fdot /. sol /. \[Epsilon] -> \[CurlyEpsilon])
  ];
  
  (* helper: add a vector increment to the current rule list *)
  keys = If[Head[solLast] === Association, Keys[solLast], solLast[[All, 1]]];
  vals = If[Head[solLast] === Association, Values[solLast], solLast[[All, 2]]];
  add[sol_, \[Delta]_] := Thread[keys -> (If[Head[sol] === Association, Values[sol], sol[[All, 2]]] + \[Delta])];
  
  (* stages *)
  k1 = f[solLast, \[Epsilon]Last];
  s12 = add[solLast, (d\[Epsilon]/2) k1];
  k2 = f[s12, \[Epsilon]Last + d\[Epsilon]/2];
  s12 = add[solLast, (d\[Epsilon]/2) k2];
  k3 = f[s12, \[Epsilon]Last + d\[Epsilon]/2];
  s3  = add[solLast, d\[Epsilon] k3];
  k4 = f[s3, \[Epsilon]Last + d\[Epsilon]];
  
  (* RK4 update *)
  Thread[keys -> (vals + d\[Epsilon] (k1 + 2 k2 + 2 k3 + k4)/6)]
];




(*The function containing the Butcher variables going into the Runge-Kutta (possibly with several b coefficients), initalised in Parameters at the moment.*)
Butcher[RKmethod_]:=(Do[c[i]=RKmethod[[1,i]],{i,1,Length[RKmethod[[1]]]}];
Do[a[i+1,ii]=RKmethod[[2,i,ii]],{i,Length[RKmethod[[2]]]},{ii,1,Length[RKmethod[[2,i]]]}];Do[Do[b[1+ii][i]=RKmethod[[3+ii,i]],{i,Length[RKmethod[[3+ii]]]}],{ii,0,Length[RKmethod]-3}];s=Length [RKmethod[[1]]];(*order of Runge-Kutta*))

(*Runge-Kutta*)
stringpred[sol_,\[Epsilon]Last_,d\[Epsilon]_]:=
(
sval=sol//Values;
skey=sol//Keys;

(*Do[k[i]=LinearSolve[J/.\[Epsilon]->\[Epsilon]Last+c[i]*d\[Epsilon]/.Thread[skey->sval+Sum[a[i,ii]k[ii],{ii,1,i-1}]d\[Epsilon]],-fdot/.\[Epsilon]->\[Epsilon]Last+c[i]*d\[Epsilon]/.Thread[skey->sval+Sum[a[i,ii]k[ii],{ii,1,i-1}]d\[Epsilon]]],{i,1,s}];
*)

Do[
  k[i] = TimeConstrained[Check[LinearSolve[
    (* System matrix at current stage *)
    J /. \[Epsilon] -> \[Epsilon]Last + c[i] * d\[Epsilon] /. 
     Thread[skey -> sval + Sum[a[i, ii] k[ii], {ii, 1, i-1}] d\[Epsilon]],
    
    (* Right-hand side vector at current stage *)
    -fdot /. \[Epsilon] -> \[Epsilon]Last + c[i] * d\[Epsilon] /. 
     Thread[skey -> sval + Sum[a[i, ii] k[ii], {ii, 1, i-1}] d\[Epsilon]]
  ],Break[]],20,Break[]],
  {i, 1, s}
];
Thread[skey->sval+d\[Epsilon] Sum[b[1][i]k[i],{i,s}]]
)


(* ::Subsubsection:: *)
(*Step control during iteration*)


IterateString := Block[{},
  
  pp = pmin;
  qq = 1;

  (* starting the procedure *)
  \[Epsilon]Last = \[Epsilon]vals[[-1]];
  badsteps = {};

  Monitor[
    While[\[Epsilon]Last < \[Epsilon]target,
      
      (* step size and new epsilon *)
      step = Min[qq/base^pp * \[CapitalDelta], \[Epsilon]target - \[Epsilon]Last];
      \[Epsilon]new = \[Epsilon]Last + step;

      (* predictor step *)
      prednew = stringpred[sol[\[Epsilon]Last], \[Epsilon]Last, step];

      Which[
        (* case 1: step too large, caught by stringfinderThrow *)
        Catch[stringfinderThrow[\[Epsilon]new, prednew]] === "Too big step",
          AppendTo[badsteps, \[Epsilon]new];
          
          If[step <= minstep,
            (* fallback: accept the step but reduce delta strongly *)
            stringfinder[\[Epsilon]new, prednew];
            sol[\[Epsilon]new] = minsolrep;
            AppendTo[\[Epsilon]vals, \[Epsilon]new];
            pp = pp + 1;
            \[CapitalDelta] = \[CapitalDelta]/2,
            
            (* otherwise just reduce step size *)
            pp = pp + 1;
            \[CapitalDelta] = \[CapitalDelta]/2
          ],

        (* case 2: normal convergence *)
        True,
          sol[\[Epsilon]new] = minsolrep;
          AppendTo[\[Epsilon]vals, \[Epsilon]new];

          If[pp > pmin,
            qq = qq + \[CapitalDelta]q;
            If[qq == base,
              qq = 1;
              pp = pp - 1;
            ]
          ];

          \[CapitalDelta] = 2 \[CapitalDelta];
      ];

      \[Epsilon]Last = \[Epsilon]vals[[-1]];
    ],

    Row@{
      "Current \[Epsilon]: ", \[Epsilon]vals[[-1]] // N,
      "   current step: ", step // N
    }
  ];
];



(* ::Subsubsection:: *)
(*Parameters*)


prec=100;
\[Epsilon]target=1;

(*Choosing Runge-Kutta method*)
RK4={{0,1/2,1/2,1},{{1/2},{0,1/2},{0,0,1}},{1/6,1/3,1/3,1/6}};
RKCK={{0,1/5,3/10,3/5,1,7/8},{{1/5},{3/40,9/40},{3/10,-9/10,6/5},{-11/54,5/2,-70/27,35/27},{1631/55296,175/512,575/13824,44275/110592,253/4096}},{37/378,0,250/621,125/594,0,512/1771},{2825/27648,0,18575/48384,13525/55296,277/14366,1/4}};
RKF={{0,1/4,3/8,12/13,1,1/2},{{1/4},{3/32,9/32},{1932/2197,-7200/2197,7296/2197},{439/216,-8,3680/513,-845/4104},{-8/27,2,-3544/2565,1859/4104,-11/40}},{16/135,0,6656/12825,28561/56430,-9/50,2/55},{25/216,0,1408/2565,2197/4104,-1/5,0}};
Butcher[RK4]

(*Interpolation order*)
interpord=3;

(*Step-size control*)
MyMaxIterations=4;
base=2;pmin=3;RecoverySpeed=1/3;
\[CapitalDelta]q=(base-1)Min[1,RecoverySpeed];

\[Beta]=0.90;

\[CapitalDelta]=1/4;
minstep=10^-3;


(* ::Subsubsection:: *)
(*Calling functions*)


SolutionFromModeConfiguration[modes_,L_]:=(
\[Epsilon]0=0;
\[Epsilon]vals={\[Epsilon]0};
GenerateSystem[modes,L];
sol[\[Epsilon]0]=Small\[Epsilon]Expansion[modes,L];
IterateString;
({#,Strings2Roots[sol[#]]}&/@\[Epsilon]vals)//Last//Last
)


(* ::Input:: *)
(*badmode={{{},{-(3/2),3/2},{-(1/2),1/2},{0},{}},{{},{},{},{0},{0}},{{},{},{},{0},{}}}*)
(*badmode ={{{3,-5,-2},{3},{0},{},{0}},{{0,1},{-(1/2),1/2},{},{},{}},{{-1,0,1},{},{},{},{}},{{-(1/2),1/2},{},{},{},{}},{{0},{},{},{},{}}}*)


(* ::Input:: *)
(*stringans=SolutionFromModeConfiguration[badmode,20]*)
