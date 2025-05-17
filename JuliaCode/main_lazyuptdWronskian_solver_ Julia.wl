(* ::Package:: *)

(* ::Subsection::Closed:: *)
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
(*solver*)


(* ::Item::Closed:: *)
(*GenerateQsystem[\[Lambda]_]*)


(* Compute the dual diagram of a Young diagram *)
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

ToTableau[path_]:=Block[{pr=path//Flatten,max},max=Max[pr];
Table[Position[pr,k]//Flatten,{k,max}]];
Quiet[Needs["Combinatorica`"]];
ToSYT[rigged_]:=ToTableau[kkrrec[ConstantArray[{1,1},Length[rigged[[1,1]]]],rigged[[2;;3]]]];


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



(* ::Item::Closed:: *)
(*GenerateWsystem[\[Lambda]_]*)


Bdegs[yd_]:=Block[{bosdeg},{bosdeg=(Reverse[yd]+Range[0,Length@yd-1]),Complement[Range[0,bosdeg//Max],bosdeg]}];
Bbos[i_,yd_]:=u^Bdegs[yd][[1]][[-i]]+Sum[b[i,k]*u^k,{k,Intersection[Range[0,Bdegs[yd][[1]][[-i]]],Bdegs[yd][[2]]]}];
Bferm[i_,yd_]:=u^Bdegs[yd][[2]][[i]];
bcoeff[yd_] := Block[
  {
    eqs, l, d, n, w, a, maxD, vars
  },
  
  (* Construct the list of equations *)
  eqs = Table[
    Block[{},
      (* Number of columns in the Young diagram to the right of a *)
      l = Length[yd] - a;
      
      (* Degree list d (truncated up to position -a - 1) *)
      d = Bdegs[yd][[1]][[;; -a - 1]];
      
      (* Values not present in d up to Max[d] *)
      maxD = Max[d];
      n = Complement[Range[0, maxD], d];
      
      (* Compute Wronskian term *)
      wron[a] = CoefficientList[
        Wron[Table[Bbos[a + i, yd], {i, 1, l}]],
        u
      ];
      
      w = CoefficientList[
        Wron[Table[Bbos[a + i, yd], {i, 1, l}]],
        u
      ]
      ;
      
      (* Subtract normalized Wronskian from YQa, and extract relevant coefficients *)
      (
        CoefficientList[YQa[a, 0, yd], u] - w / w[[-1]]
      )[[Total[d[[;; -2]]] + n - l (l - 1)/2 + 1]]
    ],
    {a, 0, Length[yd] - 1}
  ];
  
  (* Solve the resulting system for Bbos variables *)
  vars = Variables@Table[Bbos[i, yd], {i, 1, Length[yd]}];
  Solve[Flatten[eqs] == 0, vars /. u -> Nothing][[1]]
]

Wron[Flist_List] := Module[{k,mat},
  k = Length[Flist];

  mat = Table[
    Flist[[i]] /. u -> (u + hbar*((k + 1)/2 - j)),
    {i, 1, k}, {j, 1, k}
  ] /. hbar -> I;
  Det[mat]
];

GenerateWsystem[\[Lambda]_] := Block[{},
 allbcoeff = bcoeff[\[Lambda]];
 
 AllrelWronskian=(CoefficientList[YQa[0,0,\[Lambda]],u]-wron[0]/wron[0][[-1]])[[;;-2]]//Expand//(#/.Complex[0,b_]:>b)&;
bvars=allbcoeff[[All,1]];

c2bcoeff:=Solve[(Table[If[{a,s}!={0,0},(CoefficientList[YQa[a,s,\[Lambda]],u]-(w=CoefficientList[Wron[Join[Table[Bbos[a+i,\[Lambda]],{i,1,Length[\[Lambda]]-a}],Table[Bferm[j,\[Lambda]],{j,1,s}]]],u])/w[[-1]])[[;;-2]],Nothing],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}]//Flatten)==0,vars][[1]];
c2bcoeffBos=Solve[(Table[(CoefficientList[YQa[a,0,\[Lambda]],u]-wron[a]/wron[a][[-1]])[[;;-2]],{a,1,Length[\[Lambda]]-1}]//Flatten)==0,Variables[Table[YQa[a,0,\[Lambda]],{a,1,Length[\[Lambda]]-1}]]/.u->Nothing][[1]];


];



400/60//N


(* ::Item::Closed:: *)
(*init\[Theta]rep[\[Lambda]T_]*)


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



(* ::Item::Closed:: *)
(*Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]T_]*)


Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]T_]:=Block[{\[Lambda],Len},\[Lambda]=\[Lambda]T//ToYD;Len=Total[\[Lambda]];
\[CapitalLambda]init\[Theta]repUptd=init\[Theta]rep[\[Lambda]T]/.\[Theta][i_]:>If[i==(\[Lambda]T//Max),\[CapitalLambda],0];  (*The set of  q\[Theta] for the initial \[Lambda]T will be used here*)
fsymrepUptd=Table[sym[n]->Expand@Coefficient[Product[u,{i,Len-1}](u-\[CapitalLambda]),u,Len-n],{n,Len}];
ftransitUptd=Solve[(Table[If[a+s==0||Not@MemberQ[vars2,c[a,s,1]],Nothing,CoefficientList[YQa[a,s,\[Lambda]]-(YQ\[Theta][a,s,\[Lambda]]/.\[CapitalLambda]init\[Theta]repUptd),u]],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}]//Flatten)==0,vars2][[1]];
];


(* ::Item::Closed:: *)
(*Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent_, \[Lambda]Tlast_, solninterim_]*)


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




(* ::Item::Closed:: *)
(*AsymEqnsUptdStart[\[CapitalLambda]0_]*)


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





(* ::Item::Closed:: *)
(*AsymEqnsUptdInterim[\[CapitalLambda]0_]*)


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


(* ::Item:: *)
(*InterpEqnsUptd[\[CapitalLambda]0_] *)


(* Generating equations using previous order results and polynomial interpolation *)
InterpEqnsUptd[\[CapitalLambda]0_] := Block[
  {minterpord = Min[Length[\[CapitalLambda]vals] - 1, interpord]},

  (* Substitute symbolic expressions with numerical \[CapitalLambda]0 *)
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;

  (* Interpolated substitution for vars using Lagrange polynomial interpolation *)
  subnc = Thread[
    Rule[
      bvars,
      Rationalize[
        Sum[
          (bvars /. sol[\[CapitalLambda]vals[[-j]]]) *
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
  ans = (# / (# /. b[a_,k_] :> ((1 + Random[]/10000) b[a,k]/. subnc) + Random[]/10000)) & /@ 
    (AllrelWronskian /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand;

  (* Slightly randomize the interpolated coefficient values for robustness *)
  subnc = subnc /. (b[a_,k_] -> x_) :> (
    b[a,k] -> Rationalize[
      x (1 + Random[]/10^(prec/10)) + Random[]/10^(prec/10),
      10^-prec
    ]
  );

  ans
];




InterpEqnsUptdnew[\[CapitalLambda]0_] := Block[
  {
    minterpord = Min[Length[\[CapitalLambda]vals] - 1, interpord],
    symrepUptd, subnc, ans
  },
  
  (* Substitute symbolic expressions with numerical \[CapitalLambda]0 *)
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;

  (* Interpolated substitution for vars using spline interpolation *)
  subnc = Thread[
    Rule[
      vars,
      Rationalize[
        Table[
          Quiet@Predict[
            Table[
              Rule @@ {\[CapitalLambda]vals[[-j]], (v /. sol[\[CapitalLambda]vals[[-j]]])},
              {j, minterpord}
            ]
          ][\[CapitalLambda]0],
          {v, vars}
        ],
        10^-prec
      ]
    ]
  ];

  (* Build interpolated and normalized equation list from Allrel *)
  ans = (# / (# /. c[a_, s_, k_] :> ((1 + Random[]/100) c[a, s, k] /. subnc) + Random[]/100)) & /@
          (Allrel /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand;

  (* Slightly randomize the interpolated coefficient values for robustness *)
  subnc = subnc /. (c[a_, s_, k_] -> x_) :> (
    c[a, s, k] -> Rationalize[
      x (1 + Random[]/10^(prec/10)) + Random[]/10^(prec/10),
      10^-prec
    ]
  );

  ans
];



(* ::Item::Closed:: *)
(*FindSolUptd*)


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


FindSolUptdW := Block[{interstep},
  interstep = {};
  
  minsolrep = Quiet@FindRoot[
    normedrel,
    {bvars, bvars /. subnc} // Transpose,
    WorkingPrecision   -> prec,
    PrecisionGoal      -> prec,
    AccuracyGoal       -> prec/2,
    MaxIterations      -> \[Infinity],
    EvaluationMonitor  :> (AppendTo[interstep, bvars])
  ];
  
  (*AppendTo[Steps, interstep];*)
];



(* ::Item::Closed:: *)
(*GenerateSolsFromAsymptoticsUptdStart: (Not need to change)*)


coeff2root[YD_]:=Table[If[{a,s}!={0,0},Thread[CoefficientList[YQa[a,s,YD],u][[;;-2]]->CoefficientList[YQprod[a,s,YD],u][[;;-2]]],Nothing],{a,0,Length[YD]-1},{s,0,YD[[a+1]]-1}]//Flatten;
rootsfromcoeff[YD_,sol_]:=Block[{k},Table[If[{a,s}!={0,0},k=1;ReplaceAll[#,u->x[a,s,k++]]&/@(NSolve[YQa[a,s,YD]/.sol,u]//Flatten),Nothing],{a,0,Length[YD]-1},{s,0,YD[[a+1]]-1}]//Flatten];
(* generating first sample points for interpolation to work + some large \[CapitalLambda] expressions *)

GenerateSolsFromAsymptoticsUptdStart[\[Lambda]current_] := Block[{},
  
  \[CapitalLambda]vals0 = {};
  
  \[CapitalLambda]0 = IntegerPart[Sqrt[Total@\[Lambda]current] + 1];
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
      sol[\[CapitalLambda]0] = allbcoeff/.minsolrep/.symrepUptd;
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];
      ,
      {\[CapitalLambda]0, rng}
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}]
  ]
  
];





(* ::Item::Closed:: *)
(*GenerateSolsFromAsymptoticsUptdInterim: (contain lambda0)*)


GenerateSolsFromAsymptoticsUptdInterim[\[Lambda]current_, \[Lambda]last_, coefflast_] := Block[{},
  
  \[CapitalLambda]vals0 = {};
  
  (*\[CapitalLambda]0 = Max[
    IntegerPart[2 (rootsfromcoeff[\[Lambda]last, coefflast] // Values // Re // Abs // Max) + 1],
    IntegerPart[Sqrt[Total@\[Lambda]current] + 1],
    2 * (Total@\[Lambda]current)
  ] ;*)
  
  \[CapitalLambda]0 = \[CapitalLambda]0Interim;
  (* Can also use IntegerPart[Sqrt[Total@\[Lambda]current] + 1] *)
  
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) * 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;
  
  Monitor[
    Do[
      normedrel = AsymEqnsUptdInterim[\[CapitalLambda]0];
      
      FindSolUptdAsymptW;

      (* sol[\[CapitalLambda]0] := Thread[Rule[vars2, (vars2 /. subc)(vars3 /. minsolrep)]]; *)
      sol[\[CapitalLambda]0] = allbcoeff/.minsolrep/.symrepUptd;
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];
      ,
      {\[CapitalLambda]0, rng}
    ],
    Row[{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}]
  ]
  
];


(* ::Item::Closed:: *)
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


(* ::Item::Closed:: *)
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



IterateUptdInterimJulia[SYT_]:=Block[{},
 exportToJulia;
 exportToJuliaInitialData[SYT];
 Print["Initial norm: ",Norm[InterpEqnsUptd[\[CapitalLambda]0]/.sol[\[CapitalLambda]0]]];
 Print["First findroot norm: ",Norm[(InterpEqnsUptd[\[CapitalLambda]0]// ExpandAll)/.MYminsolrep]];

 juliaOutput = ExternalEvaluate[sessionJulia,juliaInputNew[SYT]];
 minsolrep=Rule@@@Transpose[{bvars,SetPrecision[juliaOutput,prec]}];
 sol[0]=minsolrep;
 AppendTo[\[CapitalLambda]vals,0];
 juliaTime = ExternalEvaluate[sessionJulia,
"[time_dummy,time_final]"];
AppendTo[savedJuliaTime,juliaTime];
]


(* ::Item::Closed:: *)
(*SolutionFromSYTUptdStart:*)


Ccoeff := Block[{},
  ccoeffat0 = c2bcoeffBos /. sol[0];
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
  GenerateWsystem[\[Lambda]start];
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

SolutionFromSYTUptdInterim[SYTcurrent_, SYTlast_, solnlast_] := Block[{
    \[Lambda]Tcurrent, \[Lambda]Tlast, \[Lambda]current, \[Lambda]last
  },
  
  Steps = {};
  
  \[Lambda]Tcurrent = SYTcurrent;
  \[Lambda]Tlast = SYTlast;
  
  \[Lambda]current = \[Lambda]Tcurrent // ToYD;
  \[Lambda]last = \[Lambda]Tlast // ToYD;
  
  GenerateQsystem[\[Lambda]current];
  GenerateWsystem[\[Lambda]current];
  Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent, \[Lambda]Tlast, solnlast];
  GenerateSolsFromAsymptoticsUptdInterim[\[Lambda]current, \[Lambda]last, solnlast];
  
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  
  
  Print["startJulia: ", SYTcurrent];
  IterateUptdInterimJulia[\[Lambda]Tcurrent];
  

  
  currentsol = {
    \[CapitalLambda]vals,
    sol[\[CapitalLambda]vals[[#]]] & /@ Range[1, Length[\[CapitalLambda]vals]],
    Ccoeff
  }
]


SolutionFromSYTUptdStepwiseWronskian[SYT_] := Block[{
    \[Lambda]Tlist
  },
  
  StepsStepwise = {};
  ansWholeIteration = {};
  predictorCorrectorList={};
  
  \[Lambda]Tlist = Table[
    Select[MemberQ[Range[1, i], #] &] /@ SYT /. {{} -> Nothing},
    {i, Count[SYT[[1]] - Range[Length[SYT[[1]]]], 0], Max[SYT]}
  ][[2 ;;]];
  
  SolutionFromSYTUptdStart[\[Lambda]Tlist[[1]]];
  AppendTo[StepsStepwise, {
    \[CapitalLambda]vals[[#]],
    Thread[bvars -> #] & /@ Steps[[#]]
  } & /@ Range[Length[Steps]]];
  AppendTo[ansWholeIteration, currentsol];
  
  Do[
    Module[{
      \[Lambda]Tcurrent, \[Lambda]Tlast
    },
      \[Lambda]Tcurrent = \[Lambda]Tlist[[i]];
      \[Lambda]Tlast = \[Lambda]Tlist[[i - 1]];
      
      SolutionFromSYTUptdInterim[
        \[Lambda]Tcurrent, \[Lambda]Tlast, currentsol[[3]]
      ];
      
      AppendTo[StepsStepwise, {
        \[CapitalLambda]vals[[#]],
        Thread[bvars -> #] & /@ Steps[[#]]
      } & /@ Range[Length[Steps]]];
      
      AppendTo[ansWholeIteration, currentsol];
    ],
    {i, 2, Length[\[Lambda]Tlist]}
  ];
  
  
  {ansWholeIteration,predictorCorrectorList}
  
  
]



(* ::Subsection:: *)
(*Run Test*)


(* ::Input::Initialization:: *)
SetDirectory[NotebookDirectory[]]
<<"mypackage.m"


singleSYTresult[yd_, k_] := Block[{},
  \[CapitalLambda]0Interim = 10;
  \[CapitalLambda]target = 0;
  startinterpord = 2;
  prec = 40;
  interpord = 1;

  

  ansWprov = Which[
    IntegerQ[k],
    L = Total[yd];
    rigs = ModestoRiggedConfig[L, #] & /@ ModesConfig[yd];
    mySYT = ToSYT /@ rigs;
      SolutionFromSYTUptdStepwiseWronskian[mySYT[[k]]],
    k === "rand",
    myrandTableau = RandomTableau[yd];
      SolutionFromSYTUptdStepwiseWronskian[myrandTableau],
    True,
      (Print["Invalid input for k"]; $Failed)
  ];
]


singleSYTresultUNIK[SYT_] := Block[{},
  \[CapitalLambda]0Interim = 1000;
  \[CapitalLambda]target = 0;
  startinterpord = 2;
  prec = 40;
  interpord = 1;
  ansWprov = SolutionFromSYTUptdStepwiseWronskian[SYT];
]


RandomPartitionWithLength[L_, n_] := Module[{parts},
  parts = Select[IntegerPartitions[L], Length[#] == n &];
  If[parts === {}, 
    Missing["NotAvailable"], 
    RandomChoice[parts]
  ]
]


(* ::Input:: *)
(*singleSYTresultUNIK[{{1, 3, 4, 6, 8, 10, 13, 15}, {2, 5, 7, 9, 14, 17, 18}, {11, 16, 19}, {12}}]*)


(* ::Input::Plain:: *)
(*yd={16,2,1,1};*)


(* ::Input:: *)
(*yd = RandomPartitionWithLength[10,4]*)


yd={3,3,3,3};


yd = RandomPartitionWithLength[20,3]


(* ::Input:: *)
(*Total[Total /@ savedJuliaTime]*)
(*Total[savedJuliaTime[[All,1]]]*)
(*Total[savedJuliaTime[[All,2]]]*)
(*Total[savedJuliaTime[[All,1]]]/Total[Total /@ savedJuliaTime]*)
(*(savedJuliaTime[[All,1]])//ListPlot[#,PlotRange->All]&*)
(*(savedJuliaTime[[All,2]])//ListPlot[#,PlotRange->All]&*)


(* ::Input:: *)
(*savedJuliaTime = {};*)
(*singel1= singleSYTresult[yd,42]//AbsoluteTiming*)
(*myrandTableau*)


(* ::Input:: *)
(*sol[0]*)


(* ::Input:: *)
(* *)


(* ::Input:: *)
(*mydata=Import["/home/zuxian/Documents/BAE_Project/yd_3_3_3_3.csv"]//ToExpression;*)
(*mydata[[1]][[indexsol=42]]//Round[#,0.001]&*)
(*ansWprov[[1]][[-1,-1]]//ConvertFromCoefficientToRoots//Round[#,0.001]&*)


MyFindRoot := Block[{interstep},
  interstep = {};
  
  MYminsolrep = Quiet@FindRoot[
    InterpEqnsUptd[\[CapitalLambda]0],
    sol[\[CapitalLambda]0] /. Rule[b_, val_] :> {b,val},
    WorkingPrecision   -> prec,
    PrecisionGoal      -> prec,
    AccuracyGoal       -> prec,
    MaxIterations      -> \[Infinity],
    EvaluationMonitor  :> (AppendTo[interstep, bvars])
  ];
  
  (*AppendTo[Steps, interstep];*)
];


(* ::Input:: *)
(*Rule@@@Transpose[{bvars,bvars/\[CapitalLambda]0}]*)


exportToJuliaInitialData[SYT_]:=Block[{},
(* Expression conversion *)
convertExprs = ((InterpEqnsUptd[h])// ExpandAll) /. b[w__, ww__] :> Symbol["b" <> ToString[w] <> ToString[ww]];
cleanExprs = ToString[#, InputForm] & /@ convertExprs;
cleanExprs = StringReplace[#, "*^" -> "*10^"] & /@ cleanExprs;

(* Variable conversion *)
convertVars = bvars /. b[w__, ww__] :> Symbol["b" <> ToString[w] <> ToString[ww]];
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
table = Transpose[{cleanVars, cleanInitb, cleanExprs}];
(*Export["/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/initial_data.csv",
  Prepend[table, {"var", "Initialvar","expression"}]];*)
  
  
Export["/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/initial_data.csv", Prepend[table, {"var", "Initialvar", "expression"}]];

filename = "/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/saved_data/" <> ToString[SYT] <> ".csv";
Export[filename, Prepend[table, {"var", "Initialvar", "expression"}]]

]



(* ::Input:: *)
(*Norm[(InterpEqnsUptd[\[CapitalLambda]0]// ExpandAll)/.MYminsolrep]*)
(*Norm[InterpEqnsUptd[\[CapitalLambda]0]/.sol[\[CapitalLambda]0]]*)


sessionJulia=StartExternalSession["Julia"];


(* ::Subitem:: *)
(*Julia version 4*)


juliaInputNew[SYT_] :=
  "
using CSV, DataFrames,BifurcationKit,Plots,JLD2,Serialization, LinearAlgebra, Base.Threads, Statistics

function load_data_and_initialize(path::String)
    global vars, vars_init, expr_funcs,df
    # Load the CSV file
    load_initial_data = CSV.read(path, DataFrame)
    # Extract the expressions and variable names
    df = load_initial_data.expression
    vars = Symbol.(vcat(load_initial_data.var, \"h\"))
    #vars_init = BigFloat.(replace.(load_initial_data.Initialvar, r\"`.*\" => \"\"))
    #vars_init = BigFloat.(replace.(load_initial_data.Initialvar, r\"\\.*\" => \"\"))
    initialvar_processed = replace.(string.(load_initial_data.Initialvar), r\"\\*10\\^\" => \"e\")
    # Convert to BigFloat
    vars_init = BigFloat.(initialvar_processed)
    # Load the expressions from the CSV file
    expr_funcs = [
        Base.eval(Expr(:->, Expr(:tuple, vars...), Meta.parse(expr)))
        for expr in df
    ]
end


# Define the general evaluation function
function G(u, p)
    args = vcat(u, p)
    return [f(args...) for f in expr_funcs]  
end;

load_data_and_initialize(\"/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/initial_data.csv\")
lambda0 = "<>ToString[\[CapitalLambda]0Interim]<>".;
u0 = Float64.(vars_init)        # Initial solution [x, y]
p0 = [lambda0];           # Corresponding h value
G(u0, 10);


prob = BifurcationProblem(G, u0, p0,1; record_from_solution = (x, p; k...) -> (Tuple(x)))

function make_opts(newton_tol,dsmax_tol)
    return ContinuationPar(
        ds = my_ds, # step size
        dsmin = my_dsmin, # minimum step size
        dsmax = dsmax_tol, # maximum step size
        p_min = 0., # minimum value of the parameter
        p_max = lambda0, # maximum value of the parameter
        max_steps = 1e5, # maximum number of steps
        newton_options = NewtonPar(tol = newton_tol, max_iterations = my_newton_iterations, verbose = false),
        detect_bifurcation = 0, 
        detect_event = 0,
        a = my_a, 
        detect_loop = false,
    )
end


function run_continuation_with_tol(prob, dsmax, method; dp_tol=0.3, initial_tol=1e-12, max_tol=1e-7)
    my_tol = initial_tol   # initial newton tolerance
    br = nothing
    while true
        br = continuation(
            prob, # defined problem
            method, # method to use e.g. PALC()
            make_opts(my_tol, dsmax), 
            normC = norm,  # norm function
            callback_newton = (state; kwargs...) -> cb(state; kwargs..., dp=dp_tol), # callback function
            verbosity = 0 # verbosity level (0 to 3)
            )
        if br.sol[end].p == 0
            #println(\"Current tolerance: $my_tol\")
            break
        elseif my_tol >= max_tol
            error(\"Failed to reach br.sol[end].p == 0 even at max tolerance.\")
        else
            @warn \"br.sol[end].p != 0 with tol=$my_tol, increasing tolerance and retrying...\"
            println(br.sol[end].p)
            my_tol *= 10
        end
    end
    return br
end

# Define the function to run continuation with a specific lambdastep 
function run_lazy(my_dp_tol)
    run = run_continuation_with_tol(
        prob, 
        1e100, # dsmax 
        PALC(tangent = Bordered()), 
        dp_tol=my_dp_tol, 
        initial_tol=my_initial_tol, 
        max_tol=1e1)
    return run
end



function my_tol_x(indices)
    if length(indices) == 0
        return 0.01  # Default tolerance if no indices are provided
    else
        return my_dx_tol  # Adjust as needed for the specific indices
    end
end

function extract_last_solution(br)
    last_point = br.branch[end]
    get_last_solution = collect(values(last_point)[1:length(u0)])
    return get_last_solution
end

function cb(state; dp, kwargs...)
    _x        = get(kwargs, :z0, nothing)
    fromNewton = get(kwargs, :fromNewton, false)
    if !fromNewton && _x !== nothing
        dp_jump = abs(_x.p - state.p)
        dx_vals = abs.(_x.u[indices] .- state.x[indices])  # Compute differences for all indices
        tol_vals = my_tol_x(indices)                      # Get tolerances for all indices
        if any(dx_vals .> tol_vals) || dp_jump > dp       # Check if any dx exceeds tolerance or dp_jump is too large
            return false
        end
    end
    return true
end

############RUN DUMMY##############
my_a =0.5;
my_ds = - 1e-2
my_dsmin= 1e-4;
my_initial_tol = 1e-3 # initial newton tolerance
my_newton_iterations = 20

time_dummy = @elapsed run_dummy = continuation(
    prob, 
    PALC(tangent = Bordered()), 
    make_opts(my_initial_tol, 1e50),
    normC = norm,
    verbosity = 0
    )
    
# auto\[Hyphen]detect which component is smallest at the first branch point
first_pt       = run_dummy.branch[1]
last_pt       = run_dummy.branch[end]
u0_vals        = collect(values(first_pt)[1:length(u0)])
uend_vals       = collect(values(last_pt)[1:length(u0)])
#indices = findall(x -> x < 2.5, abs.(u0_vals))
diff_first_last = abs.(uend_vals-u0_vals)
indices = findall(x -> x < 4, diff_first_last)
min_idx        = argmin(abs.(u0_vals))
#println(\"\[RightArrow] monitoring component #\", min_idx, \" (smallest at start)\")

####################################

################################
my_a =0.01;
my_ds = - 1e-2
my_dsmin= 1e-4;
my_initial_tol = 1e-8
my_newton_iterations = 1000
################################
println(findall(x -> x < 20, abs.(u0_vals)))
############Run While ############
my_a =0.01
my_ds = - 1e-2
my_dsmin= 1e-5
my_initial_tol = 1e-8
my_newton_iterations = 42

tol = 30 # tolerance for while
ends_greater_than_threshold = false

find_all_sol_first_less = findall(x -> x < 20, abs.(u0_vals))
time_final = @elapsed if length(find_all_sol_first_less) == 0
    global final_result = run_lazy(.1)
else
    while !ends_greater_than_threshold
        #global my_dx_tol = mean([diff_first_last[i] for i in indices]) / tol # tolerance for dx
        global my_dx_tol = 1 / tol # tolerance for dx    
        global final_result = run_lazy(50)
        global find_all_sol_first_less = findall(x -> x < 20, abs.(u0_vals))
        # Extract the values of the specified field from each solution in the branch
        global solution_differences = [abs.(diff([getfield(pt, idx) for pt in final_result.branch])) for idx in find_all_sol_first_less]
        # Check if the last value of each element in x is less than 0.1 
        global ends_greater_than_threshold = all(last(xi) < 0.01 for xi in solution_differences)
        # Print the current tol
        if !ends_greater_than_threshold
            global tol += 10
        end
    end
end

##################################
maximum_start_value = maximum(abs.(final_result.sol[1].x))
minimal_start_value = minimum(abs.(final_result.sol[1].x))
println(\"Maximum start value: \", maximum_start_value)
println(\"Minimal start value: \", minimal_start_value)
println(\"Ratio: \", maximum_start_value/minimal_start_value)
println(\"Newton tol: \", final_result.contparams.newton_options.tol)
println(\"Current tol = $tol\")
println(\"Step: \", final_result.step[end])
#println(\"Solution: \", extract_last_solution(final_result))
println(\"-----------------------------------------------------\")
df_out = DataFrame(var = string.(vars[1:end-1]), b_final_value = extract_last_solution(final_result))
CSV.write(\"/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/saved_data/result_" <>ToString[SYT]<> ".csv\", df_out)
extract_last_solution(final_result)


";


(* ::Input:: *)
(*juliaOutput = ExternalEvaluate[sessionJulia,juliaInputNew[w]]*)


(* ::Input:: *)
(*ExternalEvaluate["Shell", *)
(*"*)
(*cd /home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation*)
(*export JULIA_NUM_THREADS=4*)
(*julia runlazysolver.jl*)
(*"]*)


(* ::Subsection::Closed:: *)
(*Run all diagrams*)


SetDirectory[NotebookDirectory[]]
<<"mypackage.m"

resultyd[yd_,sInterpord_,nInterpord_,vprec_, a_, b_] := Module[{},
  
  L = Total[yd];
  rigs = ModestoRiggedConfig[L, #] & /@ ModesConfig[yd];
  mySYT = ToSYT /@ rigs;

  stepblock := Block[{},
    \[Delta] = \[CapitalLambda]Last - \[CapitalLambda]target;
    step = Which[
      \[Delta] > 2,      Round[\[Delta]/a, 0.01],
      \[Delta] > 0.02,   b,
      True,              0.1
    ];
  ];

  startinterpord = sInterpord;
  prec = vprec;          (* 40 is bad *)
  interpord = nInterpord;      (* 7 is bad *)
  \[CapitalLambda]target = 0;

  lazyuptd\[LetterSpace]stepwise\[LetterSpace]allrigg = 
   Table[
Print["Current index",k];
      Off[FrontEndObject::notavail]; 
      SolutionFromSYTUptdStepwiseWronskian[mySYT[[k]]],
      {k, Length[mySYT]}
    ];

  allroots = lazyuptd\[LetterSpace]stepwise\[LetterSpace]allrigg[[All,1]][[
      solrig = All, mystep = -1, getc = -1
    ]] // ConvertFromCoefficientToRoots;

  allroots // FindDuplicateRootPositionsOnlyRoot // Print;

  lazyuptd\[LetterSpace]stepwise\[LetterSpace]allrigg

  (* allroots // FindDuplicateRootPositionsOnlyRoot *)
]





(* ::Input:: *)
(*yd={4,2,1}*)
(*result1=resultyd[yd,2,4,40, 5,2] ;*)


(* ::Input:: *)
(*  allroots // FindDuplicateRootPositionsOnlyRoot*)


allroots


(* ::Input:: *)
(*result1[[All,1]]*)


(* ::Input:: *)
(*result1[[All,1]][[mysol=3]][[-1,2,-1]]*)
(*result1[[All,1]][[mysol=1]][[-1,2,-1]]*)


(* ::Input:: *)
(*result1[[All,1]][[mysol=-1]][[-1,2,-1]]*)
