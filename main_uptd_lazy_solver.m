(* ::Package:: *)

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
(*New lazysolver*)


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




(* ::Subsection:: *)
(*GenerateQsystem*)


GenerateQsystem[\[Lambda]_] := Block[{},
  
  (* Length of spin chain *)
  Len = Total[\[Lambda]];
  
  (* Unprotect M to avoid conflicts with Combinatorica package *)
  Unprotect[M]; ClearAll[M];

  (* Define the maximal possible domain of interest *)
  FullYoungDiagram = Block[{mm}, 
    Flatten@Table[
      mm[a, s], {a, 0, Length[\[Lambda]] - 1}, {s, 0, \[Lambda][[a + 1]] - 1}
    ] /. mm -> List
  ];
  
  (* Set domain of interest *)
  DomainOfInterest = FullYoungDiagram;
  
  (* Example of a non-standard DomainOfInterest *)
  (* DomainOfInterest = Block[{mm}, Flatten@Table[mm[a, s], {a, 0, 1}, {s, 0, 1}] /. mm -> List]; *)

  (* Function to compute M values for given YD *)
  M[a_, s_, YD_] := M[a, s, YD] = 
    Total[YD] + a s - Total[YD[[1 ;; a]]] - Total[DualDiagram[YD][[1 ;; s]]];

  (* Definition of YQa functions *)
  YQa[0, 0, YD_] := u^Total[YD] + Sum[u^(Total[YD] - k) sym[k], {k, Len}];
  
  YQa[a_, s_, YD_] := 
    u^M[a, s, YD] + Sum[c[a, s, k] u^(M[a, s, YD] - k), {k, M[a, s, YD]}];

  (* Definition of YQ\[Theta] functions *)
  YQ\[Theta][0, 0, YD_] := YQa[0, 0, YD];

  YQ\[Theta][a_, s_, YD_] := 
    Product[u - q\[Theta][a, s, k], {k, 1, M[a, s, YD]}];

  (* QQ relation computation *)
  QQrel[a_, s_, YD_] := 
    CoefficientList[
      (YQa[a, s, YD] /. u -> u + I/2) (YQa[a + 1, s + 1, YD] /. u -> u - I/2) - 
      (YQa[a, s, YD] /. u -> u - I/2) (YQa[a + 1, s + 1, YD] /. u -> u + I/2) - 
      I (M[a, s, YD] - M[a + 1, s + 1, YD]) YQa[a + 1, s, YD] YQa[a, s + 1, YD], 
      u
    ] /. Complex[0, b_] :> b;

  (* Compute all relations within the domain of interest *)
  Allrel = Monitor[
    Table[
      If[MemberQ[DomainOfInterest, {a, s}] && M[a, s, \[Lambda]] > 0, 
        QQrel[a, s, \[Lambda]], 
        Nothing
      ], 
      {a, 0, Length[\[Lambda]] - 1}, {s, 0, \[Lambda][[a + 1]] - 1}
    ], {a, s}
  ] // Flatten;

  (* Variables include coefficients of all Q-functions *)
  vars = Table[
    If[a + s == 0, Nothing, c[a, s, k]], 
    {a, 0, Length[\[Lambda]] - 1}, {s, 0, \[Lambda][[a + 1]] - 1}, {k, M[a, s, \[Lambda]]}
  ] // Flatten;

  (* Filter variables to include only those appearing in the domain of interest *)
  vars2 = DeleteCases[Variables[Allrel], sym[_]];
]



(* ::Input:: *)
(*GenerateQsystem[{4,2,1}]*)
(*Allrel*)


(* ::Subsection:: *)
(*init\[Theta]rep*)


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



(* ::Input:: *)
(*init\[Theta]rep[{{1,3,6,7},{2,5},{4}}] *)


(* ::Subsection:: *)
(*Large\[CapitalLambda]ExpansionUptdStart*)


Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]T_] := 
  Block[{\[Lambda], Len},
    
    (* Convert tableau to Young diagram and compute total length *)
    \[Lambda] = \[Lambda]T // ToYD; 
    Len = Total[\[Lambda]];

    (* Initialize q\[Theta] for the initial \[Lambda]T *)
    \[CapitalLambda]init\[Theta]repUptd = 
      init\[Theta]rep[\[Lambda]T] /. \[Theta][i_] :> 
        If[i == (\[Lambda]T // Max), \[CapitalLambda], 0];

    (* Compute sym function replacement rules *)
    fsymrepUptd = Table[
      sym[n] -> Expand@Coefficient[
        Product[u, {i, Len - 1}] (u - \[CapitalLambda]), 
        u, Len - n
      ], 
      {n, Len}
    ];

    (* Solve for Q-functions using YQa and YQ\[Theta] functions *)
    ftransitUptd = Solve[
      (
        Table[
          If[a + s == 0 || Not@MemberQ[vars2, c[a, s, 1]], 
            Nothing, 
            CoefficientList[
              YQa[a, s, \[Lambda]] - 
              (YQ\[Theta][a, s, \[Lambda]] /. \[CapitalLambda]init\[Theta]repUptd), 
              u
            ]
          ], 
          {a, 0, Length[\[Lambda]] - 1}, 
          {s, 0, \[Lambda][[a + 1]] - 1}
        ] // Flatten
      ) == 0, 
      vars2
    ][[1]];

    (* Expand relations in terms of \[CapitalLambda] *)
    anlyticUptd = Collect[
      (
        Allrel /. fsymrepUptd /. 
        c[a_, s_, k_] :> (c[a, s, k] + 
          Sum[ecc[ord][a, s, k] \[CapitalLambda]^(-ord + 1), {ord, maxord}]
        ) /. ftransitUptd
      ) // Expand, 
      \[CapitalLambda]
    ];
  ];



(* ::Input:: *)
(*Large\[CapitalLambda]ExpansionUptdStart[{{1,3,6,7},{2,5},{4}}]*)
(**)
(*?YQ\[Theta]*)
(**)
(**)


(* ::Subsection:: *)
(*Large\[CapitalLambda]ExpansionUptdInterim*)


Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tcurrent_, \[Lambda]Tlast_, solninterim_] := 
  Block[{\[Lambda]current, \[Lambda]last, Len},

    (* Convert tableaux to Young diagrams *)
    \[Lambda]current = \[Lambda]Tcurrent // ToYD;
    \[Lambda]last = \[Lambda]Tlast // ToYD;
    Len = Total[\[Lambda]current];

    (* Define q\[Theta] for the current \[Lambda]T after removing some boxes *)
    \[CapitalLambda]init\[Theta]repUptd = 
      init\[Theta]rep[\[Lambda]Tcurrent] /. \[Theta][i_] :> 
        If[i == (\[Lambda]Tcurrent // Max), \[CapitalLambda], 0];

    (* Compute sym function replacement rules *)
    fsymrepUptd = Table[
      sym[n] -> Expand@Coefficient[
        Product[u, {i, Len - 1}] (u - \[CapitalLambda]), 
        u, Len - n
      ], 
      {n, Len}
    ];

    (* Solve for updated Q-functions *)
    ftransitUptdInterim = Solve[
      (
        Table[
          If[a + s == 0 || Not@MemberQ[vars2, c[a, s, 1]], 
            Nothing, 
            CoefficientList[
              YQa[a, s, \[Lambda]current] - 
              If[
                (* Check if (a, s) is within the position of the maximum element *)
                a < Position[\[Lambda]Tcurrent, \[Lambda]Tcurrent // Max][[1, 1]] && 
                s < Position[\[Lambda]Tcurrent, \[Lambda]Tcurrent // Max][[1, 2]],
                
                (* Expression for updated YQa *)
                (u - Sum[q\[Theta][a, s, k], {k, M[a, s, \[Lambda]current]}]) 
                  YQa[a, s, \[Lambda]last] /. solninterim /. \[CapitalLambda]init\[Theta]repUptd, 
                
                (* Otherwise, use the last known YQa *)
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

    (* Expand relations in terms of \[CapitalLambda] *)
    anlyticUptdInterim = Collect[
      (
        Allrel /. fsymrepUptd /. 
        (ftransitUptdInterim /. (c[a_, s_, k_] -> x_) :> 
          (c[a, s, k] -> x + Sum[ecc[ord][a, s, k] \[CapitalLambda]^(-ord + 1), {ord, 1, maxord}]))
      ) // Expand, 
      \[CapitalLambda]
    ];
  ];



(* ::Input:: *)
(*ftransitUptdInterim*)


(* ::Input:: *)
(*Large\[CapitalLambda]ExpansionUptdInterim[{{1,3,6},{2,5},{4}}, {{1,3,6,7},{2,5},{4}}, solninterim]*)


(* ::Input:: *)
(*ftransitUptdInterim*)


(* ::Input:: *)
(*ftransitUptdInterim;*)
(*Allrel/.fsymrepUptd*)


(* ::Input:: *)
(*anlyticUptdInterim*)


(* ::Subsection:: *)
(*SubleadingOrdersUptdStart*)


(* ::Input:: *)
(*SubleadingOrdersUptdStart*)


(* ::Input:: *)
(*Series[anlyticUptd[[1]],{\[CapitalLambda], \[Infinity], maxord}]*)
(*Series[\[CapitalLambda], {\[CapitalLambda], \[Infinity], maxord - 1}] - \[CapitalLambda]*)


(* ::Input:: *)
(*SubleadingOrdersUptdStart*)


SubleadingOrdersUptdStart := Block[{},
  (* Compute subleading orders *)
  subleadUptd = Monitor[
    Table[
      Normal@Series[anlyticUptd[[k]], {\[CapitalLambda], \[Infinity], maxord}], 
      {k, Length[anlyticUptd]}
    ], k
  ];

  (* Define cutoff term for expansion *)
  cutoff = Series[\[CapitalLambda], {\[CapitalLambda], \[Infinity], maxord - 1}] - \[CapitalLambda];

  (* Compute subleading equations *)
  subleadingeqnsUptd = Monitor[
    Table[
      (subleadUptd[[k]] + cutoff)[[3]], 
      {k, Length[subleadUptd]}
    ], k
  ];

  (* Solve for subleading terms *)
  Do[
    \[CapitalLambda]sol[ord] = Solve[
      subleadingeqnsUptd[[All, ord]] == 0 /. Flatten@Table[\[CapitalLambda]sol[k], {k, ord - 1}], 
      vars2 /. c[a_, s_, k_] :> ecc[ord][a, s, k]
    ][[1]],
    {ord, maxord}
  ];
];





(* ::Subsection:: *)
(*SubleadingOrdersUptdInterim*)


(* ::Input:: *)
(*SubleadingOrdersUptdInterim*)


SubleadingOrdersUptdInterim := Block[{\[CapitalLambda]solprov, varleft},
  (* Compute subleading orders *)
  subleadUptd = Monitor[
    Table[
      Normal@Series[anlyticUptdInterim[[k]], {\[CapitalLambda], \[Infinity], maxord}], 
      {k, Length[anlyticUptdInterim]}
    ], k
  ];

  (* Define cutoff term for expansion *)
  cutoff = Series[\[CapitalLambda], {\[CapitalLambda], \[Infinity], maxord - 1}] - \[CapitalLambda];

  (* Compute subleading equations *)
  subleadingeqnsUptd = Monitor[
    Table[
      (subleadUptd[[k]] + cutoff)[[3]], 
      {k, Length[subleadUptd]}
    ], k
  ];

  (* Initialize solution list and remaining variables *)
  \[CapitalLambda]solprov = {};
  varleft = {};

  (* Solve for subleading orders iteratively *)
  Do[
    Module[{solprovprov},
      solprovprov = {};
      Do[
        AppendTo[solprovprov, Solve[
          (subleadingeqnsUptd[[All, ord]][[i]] /. \[CapitalLambda]solprov /. solprovprov // Chop) == 0, 
          Union[vars2 /. c[a_, s_, k_] :> ecc[ord][a, s, k], varleft]
        ][[1]]];

        (* Flatten solutions for better substitution *)
        solprovprov = (solprovprov // Flatten) /. (ecc[ord_][a_, s_, k_] -> x_) :> 
          (ecc[ord][a, s, k] -> (x /. (solprovprov // Flatten))),
        {i, Length[subleadingeqnsUptd[[All, ord]]]}
      ];

      (* Store solutions *)
      AppendTo[\[CapitalLambda]solprov, solprovprov];

      (* Update solutions *)
      \[CapitalLambda]solprov = (\[CapitalLambda]solprov // Flatten) /. (ecc[ord_][a_, s_, k_] -> x_) :> 
        (ecc[ord][a, s, k] -> (x /. (\[CapitalLambda]solprov // Flatten)));

      (* Track remaining variables *)
      varleft = Complement[
        Union[vars /. c[a_, s_, k_] :> ecc[ord][a, s, k], varleft], 
        \[CapitalLambda]solprov // Keys
      ];
    ], 
    {ord, maxord}
  ];

  (* Store final solutions *)
  \[CapitalLambda]solinterim = \[CapitalLambda]solprov /. (ecc[ord_][a_, s_, k_] -> x_) :> 
    (ecc[ord][a, s, k] -> (x /. \[CapitalLambda]solprov));

  (* Determine solution order *)
  solnorder = Union[
    ((If[RealValuedNumberQ[# // Values] == False, #, Nothing] & /@ \[CapitalLambda]solinterim) // Keys) /. 
      (ecc[ord_][a_, s_, k_] :> ord - 1), 
    {maxord}, 
    varleft /. (ecc[ord_][a_, s_, k_] :> ord - 1)
  ] // Min;
];


(* ::Subsection:: *)
(*AsymEqnsUptdStart*)


(* ::Input:: *)
(*AsymEqnsUptdStart[1];*)


(* Generating equations using asymptotic approximation *)
AsymEqnsUptdStart[\[CapitalLambda]0_] := Block[{},
  
  (* Replace symbols with their updated values at \[CapitalLambda]0 *)
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;
  transitUptd = ftransitUptd /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Compute updated variable replacements *)
  subnc = Thread[
    Rule[
      vars, 
      vars /. (c[a_, s_, k_] :> 
        (c[a, s, k] + Sum[\[CapitalLambda]0^(-ord + 1) (ecc[ord][a, s, k] /. \[CapitalLambda]sol[ord]), 
          {ord, maxord}]
        )
      ) /. transitUptd
    ]
  ];

  (* Compute asymptotic equations with the updated substitutions *)
  # / (1 + Abs[# /. c[a_, s_, k_] :> (c[a, s, k] /. subnc)]) & /@ 
    (Allrel /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand
];


(* ::Subsection:: *)
(*AsymEqnsUptdInterim*)


(* Generating equations using asymptotic approximation for interim values *)
AsymEqnsUptdInterim[\[CapitalLambda]0_] := Block[{},
  
  (* Replace symbols with their updated values at \[CapitalLambda]0 *)
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;
  transitUptdInterim = ftransitUptdInterim /. \[CapitalLambda] -> \[CapitalLambda]0;
  
  (* Compute updated variable replacements *)
  subnc = Thread[
    Rule[
      vars, 
      vars /. (c[a_, s_, k_] :> 
        (c[a, s, k] + Sum[
          \[CapitalLambda]0^(-ord + 1) (ecc[ord][a, s, k] /. \[CapitalLambda]solinterim), 
          {ord, solnorder}]
        )
      ) /. transitUptdInterim
    ]
  ];

  (* Compute asymptotic equations with the updated substitutions *)
  # / (1 + Abs[# /. c[a_, s_, k_] :> (c[a, s, k] /. subnc)]) & /@ 
    (Allrel /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand
];


(* ::Subsection:: *)
(*InterpEqnsUptd*)


(* Generating equations using previous order results and polynomial fit *)
InterpEqnsUptd[\[CapitalLambda]0_] := Block[{minterpord = Min[Length[\[CapitalLambda]vals] - 1, interpord]},
  
  (* Replace symbols with their updated values at \[CapitalLambda]0 *)
  symrepUptd = fsymrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0;

  (* Compute interpolated substitutions *)
  subnc = Thread[
    Rule[
      vars, 
      Round[
        Sum[
          (vars /. sol[\[CapitalLambda]vals[[-j]]]) 
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

  (* Compute interpolated equations with added small randomness *)
  # / (# /. c[a_, s_, k_] :> ((1 + Round[Random[]/100, 10^-5]) c[a, s, k] /. subnc)) & /@ 
    (Allrel /. symrepUptd /. \[CapitalLambda] -> \[CapitalLambda]0) // Expand
];





(* ::Subsection:: *)
(*FindSolUptd*)


(* ::Input:: *)
(*FindMinimum[Abs[x+1]+Abs[x+1.01]+Abs[y+1],{x,y},Method->"Newton"]*)


(* ::Input:: *)
(*minsolrep*)


(* Routine to produce solution with monitoring *)
FindSolUptd := (
  i = 0;
  {minim, minsolrep} = Monitor[
    FindMinimum[
      normedrel . normedrel, 
      {vars, vars /. subnc} // Transpose,
      
      (* Precision settings *)
      WorkingPrecision -> prec, 
      PrecisionGoal -> Infinity, 
      AccuracyGoal -> prec/2, 
      
      (* Iteration settings *)
      MaxIterations -> 50, 
      Method->Automatic;
		
      (* Uncomment for iteration monitoring *)
      (* ,EvaluationMonitor :> (i++; norm = normedrel . normedrel // N; 
         If[i > MyMaxIterations, Throw["Too big step"]]) *)
    ], 
    Row@{"Step: ", i, ",   Minim: ", norm}
  ];
);

(* Silent routine to produce solution without monitoring output *)
SilentFindSolUptd := (
  i = 0;
  {minim, minsolrep} = FindMinimum[
    normedrel . normedrel, 
    {vars, vars /. subnc} // Transpose,
    
    (* Precision settings *)
    WorkingPrecision -> prec, 
    PrecisionGoal -> Infinity, 
    AccuracyGoal -> prec/2, 
    
    (* Iteration settings *)
    MaxIterations -> 50, 
    Method -> Automatic, 
    
    (* Iteration counter without printing *)
    EvaluationMonitor :> (
      i++; 
      If[i > MyMaxIterations, Throw["Too big step"]]
    )
  ];
);


(* ::Subsection:: *)
(*GenerateSolsFromAsymptoticsUptdStart*)


(* Generate first sample points for interpolation + large \[CapitalLambda] expressions *)
GenerateSolsFromAsymptoticsUptdStart := Block[{},
  
  (* Initialize \[CapitalLambda] values *)
  \[CapitalLambda]vals0 = {};
  
  (* Generate a range of \[CapitalLambda] values for interpolation *)
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;

  (* Iterate over \[CapitalLambda] values to compute solutions *)
  Monitor[
    Do[
      (* Compute asymptotic equations at given \[CapitalLambda]0 *)
      normedrel = AsymEqnsUptdStart[\[CapitalLambda]0];

      (* Find solution for current \[CapitalLambda]0 *)
      FindSolUptd;

      (* Store the solution *)
      sol[\[CapitalLambda]0] = minsolrep;
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];

    , {\[CapitalLambda]0, rng}],
    Row@{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}
  ];
];





(* ::Subsection:: *)
(*GenerateSolsFromAsymptoticsUptdInterim*)


(* Generate sample points for interpolation with interim asymptotics *)
GenerateSolsFromAsymptoticsUptdInterim := Block[{},
  
  (* Initialize \[CapitalLambda] values *)
  \[CapitalLambda]vals0 = {};
  
  (* Generate a range of \[CapitalLambda] values for interpolation *)
  rng = Join[
    Range[\[CapitalLambda]0, \[CapitalLambda]0 + (startinterpord - 1) 1/40, 1/40]
  ] // Flatten // Union // Sort // Reverse;

  (* Iterate over \[CapitalLambda] values to compute solutions *)
  Monitor[
    Do[
      (* Compute interim asymptotic equations at given \[CapitalLambda]0 *)
      normedrel = AsymEqnsUptdInterim[\[CapitalLambda]0];

      (* Find solution for current \[CapitalLambda]0 *)
      FindSolUptd;

      (* Store the solution *)
      sol[\[CapitalLambda]0] = minsolrep;
      AppendTo[\[CapitalLambda]vals0, \[CapitalLambda]0];

    , {\[CapitalLambda]0, rng}],
    Row@{"Current \[CapitalLambda] is: ", \[CapitalLambda]0 // N}
  ];
];


(* ::Subsection:: *)
(*IterateUptd*)


(* Iteration procedure *)
IterateUptd[SYT_] := Block[{},
  
  (* Initialize parameters *)
  pp = pmin;
  qq = 1;
  step := qq / base^pp;
  
  (* Starting the procedure *)
  \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];

  Monitor[
    While[\[CapitalLambda]Last > \[CapitalLambda]target,
      
      (* If step size is too small, print status and break *)
      If[step < 10^-20, 
        Print[{SYT, step // N, \[CapitalLambda]vals // N}];
        Break[]
      ];

      (* Compute new \[CapitalLambda] value *)
      \[CapitalLambda]new = Max[\[CapitalLambda]Last - step, \[CapitalLambda]target];

      (* Generate interpolated equations *)
      normedrel = InterpEqnsUptd[\[CapitalLambda]new];

      (* Solve equations and update values based on result *)
      Which[
        Catch[SilentFindSolUptd] === "Too big step",
        pp = pp + 1,

        i > 5,
        sol[\[CapitalLambda]new] = minsolrep;
        AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new],

        True,
        sol[\[CapitalLambda]new] = minsolrep;
        AppendTo[\[CapitalLambda]vals, \[CapitalLambda]new];

        (* Adjust step size control parameters *)
        If[pp > pmin, 
          qq = qq + \[CapitalDelta]q;
          If[qq == base, qq = 1; pp = pp - 1];
        ]
      ];

      (* Update last \[CapitalLambda] value *)
      \[CapitalLambda]Last = \[CapitalLambda]vals[[-1]];
    ],
    
    (* Display status update during iteration *)
    Row@{
      "Current \[CapitalLambda] history is: ", \[CapitalLambda]vals // N,
      " current \[CapitalLambda] is: ", \[CapitalLambda]Last // N, 
      "   step is: ", step // N
    }
  ];
];



(* ::Subsection:: *)
(*SolutionFromSYTUptdStart*)


(* Solve the initial Young tableau: one row with increasing values *)
SolutionFromSYTUptdStart[SYT_] := Block[{\[Lambda]Tstart, \[Lambda]start},
  
  (* Convert tableau to Young diagram *)
  \[Lambda]Tstart = SYT;
  \[Lambda]start = \[Lambda]Tstart // ToYD;
  
  (* Generate Q-system and compute expansions *)
  GenerateQsystem[\[Lambda]start];
  Large\[CapitalLambda]ExpansionUptdStart[\[Lambda]Tstart];
  SubleadingOrdersUptdStart;
  GenerateSolsFromAsymptoticsUptdStart;
  
  (* Store computed \[CapitalLambda] values *)
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  (* Iterate to refine solutions *)
  IterateUptd[\[Lambda]Tstart];
];

(* Solve for interim Young tableaux configurations *)
SolutionFromSYTUptdInterim[SYTcurrent_, SYTlast_, solnlast_] := Block[{\[Lambda]Tinterim, \[Lambda]Tlast, \[Lambda]interim},
  
  (* Convert tableaux to Young diagrams *)
  \[Lambda]Tinterim = SYTcurrent;
  \[Lambda]Tlast = SYTlast;
  \[Lambda]interim = \[Lambda]Tinterim // ToYD;
  
  (* Generate Q-system and compute expansions for interim solution *)
  GenerateQsystem[\[Lambda]interim];
  Large\[CapitalLambda]ExpansionUptdInterim[\[Lambda]Tinterim, \[Lambda]Tlast, solnlast];
  SubleadingOrdersUptdInterim;
  GenerateSolsFromAsymptoticsUptdInterim;
  
  (* Store computed \[CapitalLambda] values *)
  \[CapitalLambda]vals = \[CapitalLambda]vals0;
  
  (* Iterate to refine solutions *)
  IterateUptd[\[Lambda]Tinterim];
];

(* Solve for Young tableaux configurations stepwise *)
SolutionFromSYTUptdStepwise[SYT_] := Block[{\[Lambda]Tlist},

  (* Generate a sequence of Young tableaux with stepwise box additions *)
  \[Lambda]Tlist = Table[
    Select[MemberQ[Range[1, i], #] &] /@ SYT /. {{ } -> Nothing},
    {i, Count[SYT[[1]] - Range[SYT[[1]] // Length], 0], SYT // Max}
  ][[2 ;;]];

  (* Solve for the first configuration *)
  SolutionFromSYTUptdStart[\[Lambda]Tlist[[1]]];

  (* Solve stepwise for subsequent configurations *)
  Do[
    SolutionFromSYTUptdInterim[\[Lambda]Tlist[[i]], \[Lambda]Tlist[[i - 1]], sol[0]],
    {i, 2, Length@\[Lambda]Tlist}
  ];

  (* Return computed solutions *)
  {
    \[CapitalLambda]vals, 
    sol[\[CapitalLambda]vals[[#]]] & /@ Range[1, Length[\[CapitalLambda]vals]], 
    (u /. Table[
      NSolve[YQa[a, 0, \[Lambda]] /. sol[\[CapitalLambda]vals[[#]]], u], 
      {a, Length[\[Lambda]] - 1}
    ]) & /@ Range[1, Length[\[CapitalLambda]vals]]
  }
];

