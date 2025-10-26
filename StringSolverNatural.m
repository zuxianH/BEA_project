(* ::Package:: *)

<<"/home/zuxian/Documents/BAE/functions.m"


(* ::Subsection:: *)
(*Solve string BAE SU(N)*)


log[z_,branch_:0,branchcut_:-Pi]:=Log[Abs[z]]+I*(Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi+2Pi*branch); (*Some initial definitions.*)
arg[z_,branch_:0,branchcut_:-Pi]:=Arg[z Exp[-I (branchcut+Pi)]]+branchcut+Pi
F[u_,branch_:0,branchcut_:-Pi]:=(-1/(2Pi*I))log[(u+I)/(u-I),branch,branchcut];
Fsym[u_,branch_:0,branchcut_:-Pi]:=F[u,branch,branchcut]-1/2;


toBetheroots[string_]:=Module[{generateValuesprocessed,generateValues,processed,result},

generateValues[v[k_, a_, s_] -> val_] := Module[{shifts},
  shifts = Table[(s - 1 - 2 j) * 0.5 I, {j, 0, s - 1}]; 
  {a, Table[-val + shift, {shift, shifts}]}
];


processed = generateValues /@ string;

result= Values[GroupBy[processed, First -> Last]];
Map[Flatten,result]

]


(* ::Subsubsection:: *)
(*Define BAElog and rootfinder with FindRoot[]*)


BAElog[k_, a_, s_, modenumber_, modes_, epsilon_] := 
  modenumber - epsilon Sum[
    Sum[
      If[{sss, jjj} != {s, k},
        Module[{term1, term2, term3},
          term1 = If[s != sss, Fsym[(2 (v[k, a, s] - v[jjj, a, sss]))/(s - sss), -1, 0], 0];
          term2 = Fsym[(2 (v[k, a, s] - v[jjj, a, sss]))/(s + sss), -1, 0];
          term3 = 2 Sum[
            If[nnn != 0,
              Fsym[(v[k, a, s] - v[jjj, a, sss])/nnn, -1, 0],
              0
            ],
            {nnn, (s - sss)/2 + 1, (s + sss)/2 - 1}
          ];
          term1 + term2 + term3
        ],
        0
      ],
      {jjj, Length[modes[[a, sss]]]}
    ],
    {sss, Length[modes[[1]]]}
  ] == -If[
    a == 1,
    L Fsym[(2 v[k, a, s])/s, -1, 0],
    Sum[
      Sum[
        Sum[
          If[nn != 0,
            Fsym[(v[k, a, s] - v[jj, a - 1, ss])/nn, -1, 0],
            0
          ],
          {nn, (s - ss)/2 + 1/2, (s + ss)/2 - 1/2}
        ],
        {jj, Length[modes[[a - 1, ss]]]}
      ],
      {ss, Length[modes[[1]]]}
    ]
  ] - If[
    a == Length[modes],
    0,
    Sum[
      Sum[
        Sum[
          If[nnnn != 0,
            Fsym[(v[k, a, s] - v[jjjj, a + 1, ssss])/nnnn, -1, 0],
            0
          ],
          {nnnn, (s - ssss)/2 + 1/2, (s + ssss)/2 - 1/2}
        ],
        {jjjj, Length[modes[[a + 1, ssss]]]}
      ],
      {ssss, Length[modes[[1]]]}
    ]
  ];

rootfinder[modes_,startvalues_,epsilon_]:=FindRoot[Table[BAElog[k,a,s,modes[[a,s,k]],modes,epsilon],{a,1,Length[modes]},{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten,{Table[v[k,a,s],{a,1,Length[modes]},{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten,
startvalues}//Transpose,WorkingPrecision->30];

rootfinder[modes_, startvalues_, epsilon_] := 
  FindRoot[
    
    (* Build the list of Bethe Ansatz Equations (in logarithmic form) *)
    Table[
      BAElog[
        k, a, s, 
        modes[[a, s, k]], 
        modes,           
        epsilon           
      ],
      {a, 1, Length[modes]},                  
      {s, 1, Length[modes[[1]]]},                  
      {k, 1, Length[modes[[a, s]]]}                
    ] // Flatten,
    
    (* Variables and their starting values for the solver *)
    {
      Table[
        v[k, a, s],                               
        {a, 1, Length[modes]},
        {s, 1, Length[modes[[1]]]},
        {k, 1, Length[modes[[a, s]]]}
      ] // Flatten,
      
      startvalues                                  (* initial guesses for roots *)
    } // Transpose,
    
    WorkingPrecision -> 30                         (* high-precision solving *)
  ];

uZeoroEpsilon[k_,a_,s_,modes_]:=Tan[-modes[[a,s,k]]*Pi/L]*s/2


(* ::Subsubsection:: *)
(*NEST*)


urootsStringHypothesisSUN[L_,modes_,\[Epsilon]Start_,\[Epsilon]Steps_]:=(*MAIN FUNCTION. Produces a list of the uroots.*)
Module[{\[Epsilon]list,ustart,solutions,finalvalue,Ma,Mas},

\[Epsilon]list=Range[\[Epsilon]Start,1,(1-\[Epsilon]Start)/\[Epsilon]Steps]; (*The list of epislon values to iterate over*)
ustart=Table[uZeoroEpsilon[k,a,s,modes],{a,1,Length[modes]},{s,1,Length[modes[[1]]]},{k,1,Length[modes[[a,s]]]}]//Flatten;

finalvalue={};
solutions=Module[{startvalues},startvalues=ustart;Nest[Module[{},
finalvalue=rootfinder[modes,startvalues,#];startvalues=finalvalue//Values//Re;#+(1-\[Epsilon]Start)/\[Epsilon]Steps]&,\[Epsilon]Start,Length[\[Epsilon]list]]];
finalvalue//Chop]


(* ::Subsubsection:: *)
(*While*)


(* Main iterative solver *)
IterativeBAEsolver[L_, modes_, \[Epsilon]Step_] := 
  Module[
    {
      epsilon = 1/1000,         (* Initial value of epsilon *)
      solution, 
      uInitial, 
      results
    },
    
    (* Initialize the first guess for uInitial *)
    uInitial = 
      Table[
        uZeoroEpsilon[k, a, s, modes],
        {a, 1, Length[modes]},
        {s, 1, Length[modes[[1]]]},
        {k, 1, Length[modes[[a, s]]]}
      ] // Flatten;
      
    results = {};
    
    While[
      epsilon <= 1,
      
      (* Solve for the current epsilon *)
      solution = rootfinder[modes, uInitial, epsilon] // Quiet;
      
      (* Store result for current epsilon *)
      AppendTo[results, {epsilon, solution}];
      
      (* Update the initial guess for the next iteration *)
      uInitial = solution // Values;
      
      (* Increment epsilon *)
      epsilon += \[Epsilon]Step;
    ];
    
    (* Return the solution for the largest epsilon, with small values chopped *)
    results[[-1]][[2]] // Chop
  ];



StringSolver[modes_,L_]:=Module[{stringsolver},
(*L=Total[yd];
modes = ModesConfig[yd];*)
stringsolver=IterativeBAEsolver[L,modes,0.005]//toBetheroots
]


(* ::Input:: *)
(*L=20*)


(* ::Input:: *)
(*StringSolver[{{{3/2,1/2},{-1,2,-2},{},{0}},{{},{-(1/2),-(5/2)},{},{}},{{},{0},{},{}}}]*)


(* ::Input:: *)
(*yd = {4,2,1};*)
(*L=7;*)
(*ModesConfig[yd]*)
(**)


(* ::Input:: *)
(*sol1=StringSolver/@ModesConfig[yd]*)


(* ::Input:: *)
(*yd = {3,2,1};*)
(*L = Total@yd;*)
(*ModesConfig[yd][[1]]*)
(*StringSolver[ModesConfig[yd][[2]]]*)


(* ::Input:: *)
(*makeDifference[eq_] := Module[{lhs, rhs},*)
(*  {lhs, rhs} = List @@ eq;*)
(*  lhs - rhs*)
(*]*)
(**)
(*stringInitial[modes_]:= Table[*)
(*        uZeoroEpsilon[k, a, s, modes],*)
(*        {a, 1, Length[modes]},*)
(*        {s, 1, Length[modes[[1]]]},*)
(*        {k, 1, Length[modes[[a, s]]]}*)
(*      ]//N // Flatten*)
(*      *)
(*stringVars[modes_]:=Table[*)
(*        v[k, a, s],                               *)
(*        {a, 1, Length[modes]},*)
(*        {s, 1, Length[modes[[1]]]},*)
(*        {k, 1, Length[modes[[a, s]]]}*)
(*      ] // Flatten*)
(*      *)
(*stringEqs[modes_]:=Table[*)
(*      BAElog[*)
(*        k, a, s, *)
(*        modes[[a, s, k]], *)
(*        modes,           *)
(*        h           (*continuation parameter*)*)
(*      ],*)
(*      {a, 1, Length[modes]},                  *)
(*      {s, 1, Length[modes[[1]]]},                  *)
(*      {k, 1, Length[modes[[a, s]]]}                *)
(*    ] // Flatten//ExpandAll     *)
(*      *)
(*      *)
(*ModesConfig[yd][[2]]//stringInitial*)
(*ModesConfig[yd][[2]]//stringVars*)
(*ModesConfig[yd][[2]]//stringEqs*)


(* ::Input:: *)
(*StringexportToJulia[modes_]:=Block[{},*)
(*mystringEqs = makeDifference/@stringEqs[modes];*)
(*convertExprs = (mystringEqs// ExpandAll) /. v[w__, ww__,www_] :> Symbol["v" <> ToString[w] <> ToString[ww]<> ToString[www]];*)
(*cleanExprs = ToString[#, InputForm] & /@ convertExprs;*)
(*cleanExprs = *)
(*  StringReplace[*)
(*    cleanExprs,*)
(*    {*)
(*      "*^" -> "*10^",*)
(*      "Pi" -> "pi",*)
(*      "Arg" -> "angle",*)
(*      "Abs" -> "abs",*)
(*      "Log" -> "log",*)
(*      "[" -> "(",*)
(*      "]" -> ")",*)
(*      "I" -> "im"*)
(*    }*)
(*  ];*)
(**)
(**)
(*(* Variable conversion *)*)
(*convertVars = stringVars[modes] /. v[w__, ww__,www_] :> Symbol["v" <> ToString[w] <> ToString[ww]<> ToString[www]];*)
(*cleanVars = ToString /@ convertVars;*)
(**)
(**)
(*(* Initial values *)*)
(*initb = stringInitial[modes];*)
(*cleanInitb = ToString[N[#, 40], InputForm] & /@ initb;*)
(*cleanInitb = *)
(*  StringReplace[*)
(*    cleanInitb,*)
(*    {*)
(*      "*^" -> "*10^",*)
(*      "`" <> ToString[40] <> "." -> ""*)
(*    }*)
(*  ];*)
(**)
(**)
(*(* Combine and export *)*)
(*table = Transpose[{*)
(*	ConstantArray[modes,Length[cleanExprs]],*)
(*	cleanVars, *)
(*	cleanInitb, *)
(*	cleanExprs}];*)
(*  *)
(*mytable =  {"modes","var", "Initialvar", "expression"};*)
(**)
(*Export["saved_data/string_initial_data.csv", Prepend[table, mytable]];*)
(**)
(*]*)
(**)
(*ModesConfig[yd][[2]]*)
(*ModesConfig[yd][[1]]//StringexportToJulia*)
(*cleanExprs//MatrixForm*)
(**)
(*convertVars*)
(*cleanInitb*)
(**)
(*table//MatrixForm*)
(**)
(*StringSolver[ModesConfig[yd][[2]]]*)
(**)
