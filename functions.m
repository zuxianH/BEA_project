(* ::Package:: *)

<<"/home/zuxian/Documents/BAE/RC.m"


ConvertFromCoefficientToRoots[solc_] := Module[
  {solList, allBetheQ, allBetheRootEqns, betheRoots},

  (* 1) If solc is a single solution (flat list of rules), wrap it in a list *)
  solList = If[ MatchQ[solc, {(_Rule)...}],
                {solc},      (* single solution \[RightArrow] list of one *)
                solc         (* already a list of solutions *)
             ];

  (* 2) Map over each solution in solList *)
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



(* ::Section:: *)
(*SYT*)


(* Transpose a Standard Young Tableau (ragged rows) *)
TransposeSYT[tab_List] := Module[
  {nrows = Length[tab], maxc, assoc, coords},
  
  If[nrows == 0, Return[{}]];
  maxc = Max[Length /@ tab];
  
  (* Map (i,j) -> entry for all existing boxes *)
  coords = Flatten[
    MapIndexed[
      Function[{row, ri},
        MapIndexed[
          ({ri[[1]], #2[[1]]} -> #1) &,
          row
        ]
      ],
      tab
    ],
    1
  ];
  assoc = Association[coords];
  
  (* New rows are old columns *)
  Table[
    With[{rowsHaving = Select[Range[nrows], Length[tab[[#]]] >= j &]},
      Table[assoc[{i, j}], {i, rowsHaving}]
    ],
    {j, 1, maxc}
  ]
]


(*English notation*)
showSYT[\[Lambda]T_]:=Graphics[Table[{(*Draw filled background box*)EdgeForm[Black],FaceForm[White],Rectangle[{s-1/2,-a-1/2},{s+1/2,-a+1/2}],(*Place the number inside*)Text[Style[\[Lambda]T[[a,s]],Small,Black],{s,-a}]},{a,1,Length[\[Lambda]T]},{s,1,Length[\[Lambda]T[[a]]]}],ImageSize->Small];
(*French notation*)
showSYT[\[Lambda]T_]:=Graphics[Table[{(*Draw filled background box*)EdgeForm[Black],FaceForm[White],Rectangle[{s-1/2,a-1/2},{s+1/2,a+1/2}],(*Place the number inside*)Text[Style[\[Lambda]T[[a,s]],Small,Black],{s,a}]},{a,Length[\[Lambda]T]},{s,Length[\[Lambda]T[[a]]]}],ImageSize->Small];


(*SYT list used in Numerical Wronskian*)
SYTlist[SYT_] := Table[
    Select[MemberQ[Range[1, i], #] &] /@ SYT /. {{} -> Nothing},
    {i, Count[SYT[[1]] - Range[Length[SYT[[1]]]], 0], Max[SYT]}
  ][[2 ;;]];


(* Promotion of SYT *)
ClearAll[InsideQ, JdtSlide, TableauPromotion, PromotionPower];

(* Is position {i,j} inside the tableau shape? *)
InsideQ[t_, {i_, j_}] := 1 <= i <= Length[t] && 1 <= j <= Length[t[[i]]];

(* Deterministic jeu de taquin slide starting from an empty box (the \[OpenCurlyDoubleQuote]hole\[CloseCurlyDoubleQuote]) *)
JdtSlide[t_List, start:{_Integer,_Integer}] := Module[
  {a = t, hole = start, right, below, move},
  a = ReplacePart[a, start -> $Hole];
  While[
    right = If[InsideQ[a, {hole[[1]], hole[[2]] + 1}], {hole[[1]], hole[[2]] + 1}, None];
    below = If[InsideQ[a, {hole[[1]] + 1, hole[[2]]}], {hole[[1]] + 1, hole[[2]]}, None];
    !(right === None && below === None),
    move = Which[
      right === None, below,
      below === None, right,
      True, If[a[[Sequence @@ right]] < a[[Sequence @@ below]], right, below]
    ];
    a = ReplacePart[a, hole -> a[[Sequence @@ move]]];
    a = ReplacePart[a, move -> $Hole];
    hole = move;
  ];
  {a, hole}
];

(* --- Promotion (\[PartialD]) --- *)
TableauPromotion[t_List] := Module[{n, pos1, slid, hole, dec},
  n    = Max @ Flatten[t];                         (* number of boxes *)
  pos1 = First @ Position[t, 1, {2}, 1];          (* locate the '1' *)
  {slid, hole} = JdtSlide[t, pos1];               (* slide the hole SE *)
  dec  = Map[Replace[#, x_Integer :> x - 1] &, slid, {2}];  (* decrement others *)
  ReplacePart[dec, hole -> n]                     (* put n in the final hole *)
];

(* Apply promotion k times *)
PromotionPower[t_List, k_Integer?NonNegative] := Nest[TableauPromotion, t, k];



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


(* ::Section::Closed:: *)
(*Rigged Configuration*)


(* --- Type A_{n-1} Cartan --- *)
CartanA[n_Integer] := Table[If[a == b, 2, If[Abs[a - b] == 1, -1, 0]], {a, n - 1}, {b, n - 1}];

(* Q_i for a partition (list of row lengths) *)
Qi[part_List, i_Integer?Positive] := Total[Min[i, #] & /@ part];

(* Sizes required by yd for B^{1,1}^L with L = Total[yd] *)
RequiredSizes[yd_List] := Module[{n = Length[yd]},
  Table[Total[yd[[a + 1 ;; n]]], {a, 1, n - 1}]
];

(* Vacancy numbers for B^{1,1} given yd and a candidate \[Nu] = {\[Nu]^(1),...,\[Nu]^(n-1)} *)
VacancyNumbersFromYD[yd_List, nus_List, iMax_: Automatic] := Module[
  {n = Length[yd], L = Total[yd], A, maxI, iRange, Q},
  If[Length[nus] =!= n - 1, Return[$Failed, Module]];
  A = CartanA[n];
  maxI = If[iMax === Automatic, Max[1, Max[0, Sequence @@ (If[# === {}, 0, Max[#]] & /@ nus)]], iMax];
  iRange = Range[maxI];
  Q[a_, i_] := Qi[nus[[a]], i];
  Table[If[a == 1, L, 0] - Sum[A[[a, b]] * Q[b, i], {b, 1, n - 1}], {a, 1, n - 1}, {i, iRange}]
];

(* Enumerate all admissible shapes \[Nu] consistent with yd (no riggings, just shapes) *)
AdmissibleShapesFromYD[yd_List] := Module[
  {n = Length[yd], sizes, partsByA, candidates, admissibleQ},
  sizes = RequiredSizes[yd];
  partsByA = IntegerPartitions /@ sizes;               (* all partitions of each required size *)
  candidates = Tuples[partsByA];                       (* all tuples (\[Nu]^(1),...,\[Nu]^(n-1)) *)
  admissibleQ[nus_] := Module[{P = VacancyNumbersFromYD[yd, nus]},
    And @@ NonNegative[Flatten[P]]
  ];
  Select[candidates, admissibleQ]
];



(* =========Basics=========*)
CartanA[n_Integer]:=Table[If[a==b,2,If[Abs[a-b]==1,-1,0]],{a,n-1},{b,n-1}];

Qi[part_List,i_Integer?Positive]:=Total[Min[i,#]&/@part];

MaxPartSize[nus_List]:=Max[0,Sequence@@(If[#==={},0,Max[#]]&/@nus)];

(*For a given word/path list that might be wrapped,get total length L*)
WordLength[path_]:=Length@Flatten[path];

(*Vacancy numbers for B^{1,1}:P^(a)_i=\[Delta]_{a1} L-Sum_b A_ab*Q_i(\[Nu]^(b))*)
VacancyFromNus[L_Integer?NonNegative,nus_List,iMax_:Automatic]:=Module[{n=Length[nus]+1,A,maxI,iRange,Q},A=CartanA[n];
maxI=If[iMax===Automatic,Max[1,MaxPartSize[nus]],iMax];
iRange=Range[maxI];
Q[a_,i_]:=Qi[nus[[a]],i];
Table[If[a==1,L,0]-Sum[A[[a,b]]*Q[b,i],{b,1,n-1}],{a,1,n-1},{i,iRange}]];

(* =========Handle flat rigging format=========*)

(*Distinct lengths present in a partition,sorted DESC (e.g.{2,1})*)
LengthsDesc[part_List]:=Reverse@Sort@DeleteDuplicates[part];

(*Split a flat rig list into per-length chunks in DESC length order.Example:part=(2,1) and rigFlat={j2,j1}-><|2->{j2},1->{j1}|>*)
SplitRigsByLength[rigFlat_List,part_List]:=Module[{lens=LengthsDesc[part],pos=1,assoc=<||>,m},Do[m=Count[part,l];
assoc[l]=If[m==0,{},Take[rigFlat,{pos,pos+m-1}]];
pos+=m,{l,lens}];
assoc];

(*Rejoin per-length lists back to one flat list in DESC length order*)
JoinRigsByLength[assoc_Association,part_List]:=Module[{lens=LengthsDesc[part]},Flatten[assoc/@lens]];

(*Flip riggings for ONE color a:r->sort(P_i-reverse(r)) per length i*)
FlipOneColor[rigFlat_List,part_List,pRow_List]:=Module[{assoc=SplitRigsByLength[rigFlat,part],lens},lens=Keys[assoc];
Do[assoc[l]=With[{r=assoc[l],p=pRow[[l]]},Sort[p-Reverse[r]]],{l,lens}];
JoinRigsByLength[assoc,part]];

(* =========Flip a single configuration and a whole list=========*)

(*One config has the shape:{path,nusByColor,rigsByColor}*)
FlipConfig[config_]:=Module[{path,nus,rigs,L,P,flipped},{path,nus,rigs}=config;
L=WordLength[path];
P=VacancyFromNus[L,nus];(*rows:colors a=1..N-1;cols:i=1..maxLen*)flipped=Table[If[nus[[a]]==={}||rigs[[a]]==={},{},FlipOneColor[rigs[[a]],nus[[a]],P[[a]]]],{a,Length[nus]}];
{path,nus,flipped}];

(*Map over an entire dataset (list of configs)*)
FlipAll[data_List]:=FlipConfig/@data;



(* =========Counting========= *)

(* Multiplicity map: how many rows of each length in a partition *)
MultiplicityByLength[part_List] := Counts[part];

(* Safe indexer: return 0 if P does not have entry i *)
PAt[pRow_List, i_Integer?Positive] := If[i <= Length[pRow], pRow[[i]], 0];

(* Count riggings for ONE color a:
   product over lengths i of Binomial(P_i + m_i, m_i) *)
CountRiggingsOneColor[part_List, pRow_List] := Module[
  {mult = MultiplicityByLength[part]},
  If[part === {} || pRow === {}, 1,
    Times @@ (Binomial[PAt[pRow, #] + mult[#], mult[#]] & /@ Keys[mult])
  ]
];

(* Per-color counts for a single configuration {path, nusByColor, rigsByColor} *)
CountRiggingsByColor[config_] := Module[
  {path, nus, rigs, L, P},
  {path, nus, rigs} = config;
  L = WordLength[path];
  P = VacancyFromNus[L, nus]; (* rows: colors; cols: i = 1..maxLen *)
  Table[
    CountRiggingsOneColor[nus[[a]], P[[a]]]
    , {a, Length[nus]}
  ]
];

(* Total number of riggings for a single configuration *)
CountRiggingsConfig[config_] := Times @@ CountRiggingsByColor[config];

(* Map over a dataset (list of configs) *)
CountRiggingsAll[data_List] := CountRiggingsConfig /@ data;

(* Optional: return both per-color vector and total *)
CountRiggingsSummary[config_] := Module[
  {per = CountRiggingsByColor[config]},
  <|"PerColor" -> per, "Total" -> Times @@ per|>
];



ClearAll[WeaklyIncreasingTuples, AssembleRowByLens, RigsForStringConfigSorted];

(* weakly increasing m-tuples from 0..P *)
WeaklyIncreasingTuples[P_Integer?NonNegative, m_Integer?NonNegative] :=
  Which[
    m == 0, {{}},
    P < 0, {},
    True, Select[Tuples[Range[0, P], m], OrderedQ[#, LessEqual] &]
  ];

(* Given one string row (e.g. {1,1,1,1,1,1}), a list of distinct lengths `lens`
   and the chosen rig-lists `rowsByLen` in the same order as `lens`,
   assemble a rig row respecting the ORIGINAL order of occurrences. *)
AssembleRowByLens[stringRow_List, lens_List, rowsByLen_List] :=
 Module[{ptr, len2rig},
  ptr = ConstantArray[1, Length[lens]];                 (* per-length pointers *)
  len2rig = AssociationThread[lens, rowsByLen];         (* length -> rig list *)
  Table[
    With[{lenKey = stringRow[[j]],
          k = ptr[[First@First@Position[lens, stringRow[[j]]]]]},
      ptr[[First@First@Position[lens, lenKey]]] = k + 1;
      len2rig[lenKey][[k]]
    ],
    {j, Length[stringRow]}
  ]
];

RigsForStringConfigSorted[yd_, string_] := Block[
  {stringmatrix, holes, perRowChoices, lens, counts, choicesByLen, tuplesByLen, assembledRows},

  (* ===  holes computation verbatim === *)
  stringmatrix =
    Table[Count[string[[i]], jj], {i, Length[string] - 1}, {jj, Max[string // Flatten]}];

  holes =
    Delete[-Cartan[Length[#]] . # . Kernel[Length[#[[1]]]],
      {{1}, {-1}}] & @ (Append[
        Prepend[stringmatrix,
          SparseArray[1 -> (AugmentedYoungD[yd] // First // First),
            Length[stringmatrix[[1]]]]],
        ConstantArray[0, Length[stringmatrix[[1]]]]
      ]);

  (* For each i-row in `string`, enumerate admissible weakly-increasing per-length choices *)
  perRowChoices =
    Table[
      counts = Counts[string[[i]]];                      (* multiplicity by length *)
      lens   = Keys[counts];                             (* distinct lengths appearing in this row *)
      choicesByLen =
        Table[
          WeaklyIncreasingTuples[holes[[i, len]], counts[len]],
          {len, lens}
        ];
      If[MemberQ[choicesByLen, {}],
        {},                                             (* no admissible riggings for this row *)
        tuplesByLen = Tuples[choicesByLen];             (* Cartesian product across lengths *)
        Map[
          Function[rowByLen,
            AssembleRowByLens[string[[i]], lens, rowByLen]
          ],
          tuplesByLen
        ]
      ],
      {i, Length[string]}
    ];

  If[MemberQ[perRowChoices, {}],
    {},                                                (* some row has no choices -> none overall *)
    assembledRows = Tuples[perRowChoices];             (* combine across rows *)
    (* wrap to {path, string, rigs} format *)
    {{ConstantArray[1, Total[yd]]}, string, #} & /@ assembledRows
  ]
];



(* --- helper: robust scalar extractor for P_i --- *)
ClearAll[PiScalar];
PiScalar[holesRow_, len_Integer?Positive] :=
  Module[{val},
    If[len > Length[holesRow], 0,
      val = holesRow[[len]];
      Which[
        IntegerQ[val], val,
        ListQ[val], First@Flatten[val],   (* unwrap {8} -> 8, {{8}} -> 8 *)
        True, 0
      ]
    ]
  ];

(* uniform random weakly-increasing m-tuple from 0..P *)
ClearAll[RandomWeaklyIncreasingTuple];
RandomWeaklyIncreasingTuple[P_Integer?NonNegative, m_Integer?NonNegative] :=
  Which[
    m == 0, {},
    P < 0, $Failed,
    True,
    Module[{s},
      s = Sort @ RandomSample[Range[P + m], m];  (* stars & bars *)
      s - Range[m]
    ]
  ];

(* one random rig row; handle empty rows and use robust P_i *)
ClearAll[RandomRigRowByLens];
RandomRigRowByLens[stringRow_List, holesRow_List] :=
 Module[{counts, lens, rowsByLen, Pi, mi},
  If[stringRow === {}, Return[{}, Module]];   (* empty string row *)
  counts = Counts[stringRow];
  lens   = Keys[counts];
  rowsByLen = Table[
    Pi = PiScalar[holesRow, len];            (* <-- robust scalar P_i *)
    mi = counts[len];
    With[{r = RandomWeaklyIncreasingTuple[Pi, mi]},
      If[r === $Failed, Return[$Failed, Module], r]
    ],
    {len, lens}
  ];
  AssembleRowByLens[stringRow, lens, rowsByLen]
];



(* --- Inverse map: rigged -> modes ------------------------------------ *)
RiggedToModes[rigged_] := 
  Module[
    {
      L, strings, riggings, 
      r, sMax, MrowLens, firstRow, lastRow, Mmatrix,
      holes, limits, modes
    },
    
    (* 1. Basic unpacking *)
    L = Length[rigged[[1, 1]]];              (* chain length *)
    strings = rigged[[2]];                   (* e.g. {{2,1}, {1}, {}} *)
    riggings = rigged[[3]];                  (* e.g. {{0,0}, {0}, {}} *)
    r = Length[strings];                     (* number of rows *)
    sMax = Max @ Flatten[ strings /. {} -> 0 ];  (* max string length *)

    (* 2. Multiplicity matrix M_{a,s} ----------------------------------- *)
    MrowLens = Table[
      Count[strings[[a]], s],
      {a, r}, {s, sMax}
    ];

    firstRow = ConstantArray[0, sMax];
    firstRow[[1]] = L;

    lastRow = ConstantArray[0, sMax];

    Mmatrix = PadRight @ Join[
      {firstRow},
      MrowLens,
      {lastRow}
    ];

    (* 3. Hole numbers and limits H_{a,s}, (H+M)/2 - 1/2 --------------- *)
    holes = - Cartan[ Length[Mmatrix] ] . Mmatrix . Kernel[sMax];

    limits = ( (Delete[holes, {{1}, {-1}}] + MrowLens)/2 ) - 1/2;

    (* 4. Recover modes: mode = rigging - limits + k - 1 --------------- *)
    modes = Table[
      Module[
        {
          occ = ConstantArray[0, sMax],
          rowModes = Table[ {}, {s, sMax} ]
        },
        
        Do[
          With[
            { s = strings[[a, n]] },
            
            occ[[s]]++;
            
            AppendTo[
              rowModes[[s]],
              riggings[[a, n]] - limits[[a, s]] - 1 + occ[[s]]
            ]
          ],
          {n, Length[strings[[a]]]}
        ];
        
        Reverse[rowModes]    (* put longer strings first, like Modesto *)
      ],
      {a, r}
    ];

    (* 5. Drop completely empty rows ----------------------------------- *)
    modes = Select[
      modes,
      AnyTrue[#, (# =!= {}) &] &
    ];

    (* 6. Reverse each row so the longest strings come first ---------- *)
    modes = Map[Reverse, modes];
    
    modes
  ];



(* ::Section::Closed:: *)
(*RiggedSYT*)


(* Path \[LeftRightArrow] Tableaux *)
ToCrystalPath[stb_]:=Block[{len=Length[stb//Flatten]},Table[{{Position[stb,k][[1,1]]}},{k,len}]];
ToTableau[path_]:=Block[{pr=path//Flatten,max},max=Max[pr];
Table[Position[pr,k]//Flatten,{k,max}]];
Quiet[Needs["Combinatorica`"]];
(* Generating rigged *)
ToRigged[SYT_]:=rkkrec[ToCrystalPath[SYT],Length[SYT//ToYD]];
(* generating SYT from rigged *)
ToSYT[rigged_]:=ToTableau[kkrrec[ConstantArray[{1,1},Length[rigged[[1,1]]]],rigged[[2;;3]]]];

(* Order rows: length \[DownArrow] ; within same length, rigging \[UpArrow] *)
ClearAll[OrderRiggingsAsc];
OrderRiggingsAsc[rc_] := Module[{ans = rc, pairs},
  Do[
    pairs = Transpose[{ans[[2, a]], ans[[3, a]]}];
    (* length descending, then rigging ascending *)
    pairs = SortBy[pairs, {-First[#] &, Last[#] &}];
    ans[[2, a]] = pairs[[All, 1]];
    ans[[3, a]] = pairs[[All, 2]];
  , {a, Length[ans[[2]]]}];
  ans
];

(* Exact-inverse version of ToRigged: compute RC, then normalize *)
ClearAll[ToRiggedExact];
ToRiggedExact[SYT_] := Module[{path, rank, rc},
  path = ToCrystalPath[SYT];
  rank = Max[Flatten[path]];
  rc = rkkrec[path, rank];
  OrderRiggingsAsc[rc]
];


(* ::Section::Closed:: *)
(*Modes number*)


(* Assumes AdmissibleModes[yd] returns {PList, MList} where
   PList[[i]] is the matrix of bounds P_{a,s} for the i-th M
   and MList[[i]] is the corresponding matrix of multiplicities m_{a,s}. *)

ModesConfig1[yd_] := Module[
  {PList, MList},
  
  (* 1) get the list of vacancy\[Dash]bounds and M\[Dash]matrices *)
  {PList, MList} = AdmissibleModes[yd];
  
  (* 2) for each admissible M, build all riggings *)
  Flatten[
    Table[
      Module[{P = PList[[i]], M = MList[[i]], blocks},
        
        (* build a 1D list of \[OpenCurlyDoubleQuote]blocks\[CloseCurlyDoubleQuote] each = Subsets[ allowedRange, {multiplicity} ] *)
        blocks = Flatten[
          Table[
            Subsets[
              Range[-P[[a, s]], P[[a, s]]],
              { M[[a, s]] }
            ],
            {a, 1, Length[P]},
            {s, 1, Length[P[[1]]]}
          ],
          1
        ];
        
        (* take the Cartesian product over all blocks *)
        Tuples[blocks]
      ],
      {i, Length[PList]}
    ],
    1  (* flatten over all i *)
  ]
];



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






(* Code finding all rigged configurations for a given Young diagram *)
ModesConfig[yd_] := Module[{},
  Modes = AdmissibleModes[yd][[1]];
  Mmatrices = AdmissibleModes[yd][[2]];
  
  Table[
    Tuples[
      Table[
        Tuples[
          Table[
            Subsets[
              Range[-Modes[[i]][[j]][[k]], Modes[[i]][[j]][[k]]],
              {Total[Mmatrices[[i]][[j]][[k]]]}
            ],
            {k, Length[Modes[[i]][[j]]]}
          ]
        ],
        {j, Length[Modes[[i]]]}
      ]
    ],
    {i, Length[Modes]}
  ] // Catenate
]



ModestoRiggedConfig[L_,modes_]:=Module[{Mmatrix,limits,deleteFirstLastLine},
Mmatrix=PadRight[Append[Prepend[Table[Length[modes[[i,j]]],{i,Length[modes]},{j,Length[modes[[i]]]}],SparseArray[1->L,1]],{0}]];

deleteFirstLastLine[x_]:=Delete[x,{{1},{-1}}];
limits=1/2 deleteFirstLastLine[-Cartan[Length[Mmatrix]] . Mmatrix . Kernel[Length[Mmatrix[[1]]]]+Mmatrix/.{0->{}}]-1/2;

Prepend[

Append[{}]/@(Table[{Table[ConstantArray[i,Length[modes[[j,i]]]],{i,Sort[Range[Length[modes[[j]]]],Greater]}]//Catenate,Table[limits[[j,i]]+modes[[j,i,k]]+1-k,{i,Sort[Range[Length[modes[[j]]]],Greater]},{k,Length[modes[[j,i]]]}]//Catenate},{j,Length[modes]}]//Transpose)


,{ConstantArray[1,L]}]

]





(* ::Section::Closed:: *)
(*CompareRootsFunction*)


DistanceMeasure[bethe_List, string_List] := 
 Module[{p, defeats, constraints},
  
  (* Distance matrix between Bethe and string roots *)
  p = DistanceMatrix[bethe,string, DistanceFunction->EuclideanDistance];
  
  (* Objective function: minimize total weighted cost *)
  defeats = Total[\!\(\*
TagBox[
StyleBox[
RowBox[{
RowBox[{"Inactive", "[", "Times", "]"}], "[", 
RowBox[{"p", ",", "x"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\), 2];

  (* Constraints: doubly stochastic matrix *)
  constraints = {
    Total[x] - 1 == 0,
    Total[x, {2}] - 1 == 0,
    x \[VectorGreaterEqual] 0
  };
  
  (* Solve the linear optimization and return absolute minimum value *)
  Abs @ LinearOptimization[
     defeats, constraints, 
     x \[Element] Matrices[Dimensions[p]], 
     "PrimalMinimumValue",Method->"CLP"
  ]
]


FindFlipDistances[result_] := 
 Module[{data, flipped, mapping, mappingClean, distancedataflip, 
   nonzeroPositions, nonzeroValues, uniqueBad, goodValues},

  (* Extract data *)
  data = result[["DataRiggeds"]];
  flipped = FlipAll[data];

  (* Build mapping between data and flipped *)
  mapping = MapIndexed[
     With[{pos = Position[data, #1]},
       If[pos === {}, 
        {#2[[1]], None}, 
        {#2[[1]], pos[[1, 1]]}
        ]
       ] &, 
     flipped
     ];

  (* Remove unmapped entries *)
  mappingClean = Select[mapping, FreeQ[#, None] &];

  (* Compute distances between Bethe roots and flipped ones *)
  distancedataflip = 
   Table[
    Round[
      DistanceMeasure[
        result[["DataBethe"]][[mappingClean[[k, 1]], 1]],
        -result[["DataBethe"]][[mappingClean[[k, 2]], 1]]
      ],
      10^-4
    ],
    {k, Length[mappingClean]}
   ] // N // Chop;

  (* --- BAD VALUES: nonzero distances --- *)
  nonzeroPositions = Flatten@Position[distancedataflip, x_ /; x != 0];
  nonzeroValues = 
   Thread[{mappingClean[[nonzeroPositions]], 
     distancedataflip[[nonzeroPositions]]}];

  uniqueBad = 
   DeleteDuplicatesBy[
    nonzeroValues /. {{a_, b_}, d_} :> {Sort[{a, b}], d},
    First
    ];

  (* --- GOOD VALUES: complement --- *)
  goodValues = 
   Complement[
     Thread[{mappingClean, distancedataflip}] /. {{a_, b_}, d_} :> {Sort[{a, b}], d},
     uniqueBad
   ];

  <|
   "BadValues" -> uniqueBad,
   "GoodValues" -> goodValues
  |>
]



ClearAll[ComputeKKRDistance];
ComputeKKRDistance[checksyt_List, result_Association, level_] := 
 Module[{allroots, allstrings, allstringConfig, KKRMap, 
   minimunCorrespond, distancesKKR, distancesMin, PlotMin, PlotKKR},

  (* extract relevant data *)
  allroots = 
   result[["DataBethe"]][[
     FirstPosition[result[["DataSYT"]], #] & /@ checksyt // Flatten]];

  (* get all string solutions and configs *)
  allstrings = GetAllStringSol[checksyt[[1]]];
  allstringConfig = ToSYT /@ GetAllStringConfig[checksyt[[1]]];

  (* KKR predicted map *)
  KKRMap = 
   Table[{FirstPosition[checksyt, allstringConfig[[k]], None][[1]], k},
    {k, Length@allstringConfig}] // Sort;

  (* numerical minimum-distance correspondence *)
  minimunCorrespond = 
   Table[{kk, 
     PositionSmallest[
        DistanceMeasure[
           allroots[[All, level]][[kk]], #] & /@ (allstrings[[All, level]])] //
       First},
     {kk, Length@allroots[[All, 1]]}];

  (* distance values for both mappings *)
  distancesKKR = 
   Table[DistanceMeasure[
     allroots[[KKRMap[[i, 1]], level]],
     allstrings[[KKRMap[[i, 2]], level]]],
    {i, Length[KKRMap]}];

  distancesMin = 
   Table[DistanceMeasure[
     allroots[[minimunCorrespond[[i, 1]], level]],
     allstrings[[minimunCorrespond[[i, 2]], level]]],
    {i, Length[minimunCorrespond]}];

  (* plots with level label and distance *)
  PlotMin = Table[
    ComplexListPlot[
     {allroots[[minimunCorrespond[[i, 1]], level]],
      allstrings[[minimunCorrespond[[i, 2]], level]]},
     PlotRange -> All,AspectRatio->1,
PlotLegends->{"Bethe roots","String roots"},
     Frame -> True,
     PlotLabel -> 
      StringJoin[
       "Minimum | Level ", ToString[level],
       " | Index ", ToString[i],
       " | Distance = ", ToString[distancesMin[[i]], InputForm]
      ]
     ],
    {i, Length[minimunCorrespond]}];

  PlotKKR = Table[
    ComplexListPlot[
     {allroots[[KKRMap[[i, 1]], level]],
      allstrings[[KKRMap[[i, 2]], level]]},
     PlotRange -> All,AspectRatio->1,
PlotLegends->{"Bethe roots","String roots"},
     Frame -> True,
     PlotLabel -> 
      StringJoin[
       "KKR | Level ", ToString[level],
       " | Index ", ToString[i],
       " | Distance = ", ToString[distancesKKR[[i]], InputForm]
      ]
     ],
    {i, Length[KKRMap]}];

  (* return everything neatly *)
  <|
   "Strings" -> allstrings,
   "Roots" -> allroots,
   "KKRMap" -> KKRMap,
   "MinimumMap" -> minimunCorrespond,
   "DistancesKKR" -> distancesKKR,
   "DistancesMinimum" -> distancesMin,
   "PlotMin" -> PlotMin,
   "PlotKKR" -> PlotKKR
   |>
  ]



ClearAll[CheckKKRMinimum];
CheckKKRMinimum[syt_] := Module[
  {
    allstringsol, stringsol, bethesol, listofdistance,
    minpositionindex, allriggeds, kkrindex, checkKkRMinimum
  },
  
  (* Generate all relevant data *)
  allstringsol = GetAllStringSol[syt];
  stringsol = GetStringSol[syt];
  bethesol = GetRootsFromSYT[syt];
  
  (* Compute total distance for each string solution *)
  listofdistance =  Table[
     Table[
       DistanceMeasure[
         Transpose[{allstringsol[[ww]], bethesol}][[kk, 1]],
         Transpose[{allstringsol[[ww]], bethesol}][[kk, 2]]
       ],
       {kk, Length[ToYD[syt]] - 1}
     ],
     {ww, Length[allstringsol]}
  ][[All,1]];
  
  (* Find minimal distance position *)
  minpositionindex = First@First@PositionSmallest[listofdistance, 1];
  
  (* Compute KKR index *)
  allriggeds = GetAllStringConfig[syt];
  kkrindex = First@First@Position[allriggeds, ToRiggedExact[syt]];
  
  (* Compare *)
  checkKkRMinimum = kkrindex == minpositionindex;
  
  <|
"SYT"->syt,
    "IsKKRMinimum" -> checkKkRMinimum,
"KKRIndex" -> kkrindex,
    "MinIndex" -> minpositionindex,
    "MinDistance" -> listofdistance[[minpositionindex]],
    "KKRDistance" -> listofdistance[[kkrindex]],
    "BestStringSol" -> allstringsol[[minpositionindex]],
    "KKRStringSol" -> allstringsol[[kkrindex]], 
"SYTSol"->bethesol
  |>
]


(* ::Section:: *)
(*LoadResults*)


ExtractSYTFromFile[file_]:=StringCases[
file ,
  ("result_" ~~ x__ ~~ ".csv" :> x)
]//First//ToExpression


(* ::Subsection:: *)
(*SetUpQsystem*)


Fsym[x_,-1,0]:=(1/Pi)ArcTan[x];
MM[a_,s_,YD_]:=MM[a,s,YD]=Total[YD]+a s-Total[YD[[1;;a]]]-Total[DualDiagram[YD][[1;;s]]];
YQa[0,0,YD_]:=u^Total[YD]+Sum[u^(Total[YD]-k) sym[k],{k,Total[YD]}];
YQa[a_,s_,YD_]:=u^MM[a,s,YD]+Sum[c[a,s,k]u^(MM[a,s,YD]-k),{k,MM[a,s,YD]}];
YQ\[Theta][0,0,YD_]:=YQa[0,0,YD];
YQ\[Theta][a_,s_,YD_]:=Product[u-q\[Theta][a,s,k],{k,1,MM[a,s,YD]}];
QQrel[a_,s_,YD_]:=
CoefficientList[(YQa[a,s,YD]/.u->u+I/2)(YQa[a+1,s+1,YD]/.u->u-I/2)-(YQa[a,s,YD]/.u->u-I/2)(YQa[a+1,s+1,YD]/.u->u+I/2)-I(MM[a,s,YD]-MM[a+1,s+1,YD])YQa[a+1,s,YD]YQa[a,s+1,YD],u]//(#/.Complex[0,b_]:>b)&;
YQprod[a_,s_,YD_]:=Product[u-x[a,s,k],{k,1,MM[a,s,YD]}];
coeff2root[YD_]:=Table[If[{a,s}!={0,0},Thread[CoefficientList[YQa[a,s,YD],u][[;;-2]]->CoefficientList[YQprod[a,s,YD],u][[;;-2]]],Nothing],{a,0,Length[YD]-1},{s,0,YD[[a+1]]-1}]//Flatten;
rootsfromcoeff[YD_,sol_]:=Block[{k},Table[If[{a,s}!={0,0},k=1;ReplaceAll[#,u->x[a,s,k++]]&/@(NSolve[YQa[a,s,YD]/.sol,u]//Flatten),Nothing],{a,0,Length[YD]-1},{s,0,YD[[a+1]]-1}]//Flatten];

Bdegs[yd_]:=Block[{bosdeg},{bosdeg=(Reverse[yd]+Range[0,Length@yd-1]),Complement[Range[0,bosdeg//Max],bosdeg]}]
Bbos[i_,yd_]:=u^Bdegs[yd][[1]][[-i]]+Sum[b[i,k]*u^k,{k,Intersection[Range[0,Bdegs[yd][[1]][[-i]]],Bdegs[yd][[2]]]}]
Bferm[i_,yd_]:=u^Bdegs[yd][[2]][[i]]

Wron[Flist_List] := Module[{k,mat},
  k = Length[Flist];
  mat = Table[
    Flist[[i]] /. u -> (u + hbar*((k + 1)/2 - j)),
    {i, 1, k}, {j, 1, k}
  ] /. hbar -> I;
  Det[mat]
]
Csystem[\[Lambda]_]:=(Allrel=Monitor[Table[If[MemberQ[DomainOfInterest,{a,s}]&&MM[a,s,\[Lambda]]>0,QQrel[a,s,\[Lambda]],Nothing],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}],{a,s}]//Flatten;
(* vars have coefficients of all Q-functions *)
vars=Table[If[a+s==0,Nothing,c[a,s,k]],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1},{k,MM[a,s,\[Lambda]]}]//Flatten;
(* only those appearing in domain of interest *)
vars2=DeleteCases[Variables[Allrel],sym[_]];
)

Bsystem[\[Lambda]_]:=(b2ccoeff=Block[{eqs},eqs=Table[Block[{l,d,n},l=Length[\[Lambda]]-a;d=Bdegs[\[Lambda]][[1]][[;;-a-1]];n=Complement[Range[0,d//Max],d];
(CoefficientList[YQa[a,0,\[Lambda]],u]-(wron[a]=CoefficientList[Wron[Table[Bbos[a+i,\[Lambda]],{i,1,l}]],u])/wron[a][[-1]])[[(d[[;;-2]]//Total)+n-l (l-1)/2+1]]],{a,Range[0,Length[\[Lambda]]-1]//Reverse}];Solve[(eqs//Flatten)==0,Variables[#]&@Table[Bbos[i,\[Lambda]],{i,1,Length[\[Lambda]]}]/.u->Nothing][[1]]];
BcoeffWronskian=b2ccoeff;
AllrelWronskian=(CoefficientList[YQa[0,0,\[Lambda]],u]-wron[0]/wron[0][[-1]])[[;;-2]]//Expand//(#/.Complex[0,b_]:>b)&;
bvars=BcoeffWronskian[[All,1]];

(*c2bcoeff:=Solve[(Table[If[{a,s}!={0,0},(CoefficientList[YQa[a,s,\[Lambda]],u]-(w=CoefficientList[Wron[Join[Table[Bbos[a+i,\[Lambda]],{i,1,Length[\[Lambda]]-a}],Table[Bferm[j,\[Lambda]],{j,1,s}]]],u])/w[[-1]])[[;;-2]],Nothing],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}]//Flatten)==0,vars][[1]];*)
c2bcoeffBos=Solve[(Table[(CoefficientList[YQa[a,0,\[Lambda]],u]-wron[a]/wron[a][[-1]])[[;;-2]],{a,1,Length[\[Lambda]]-1}]//Flatten)==0,Variables[Table[YQa[a,0,\[Lambda]],{a,1,Length[\[Lambda]]-1}]]/.u->Nothing][[1]];

J=D[AllrelWronskian/.(sym[n_]:>If[n==1,-\[CapitalLambda],0]),{bvars}];
H=D[#/.(sym[n_]:>If[n==1,-\[CapitalLambda],0]),{bvars,2}]&/@AllrelWronskian;
dddf=D[#,{bvars,3}]&/@AllrelWronskian;
fdot=D[AllrelWronskian/.(sym[n_]:>If[n==1,-\[CapitalLambda],0]),\[CapitalLambda]];
)

GenerateQsystemW[\[Lambda]_]:=Block[{},
((* Length of spin chain *)
Len=Total[\[Lambda]];
(* domain of interest is the values of {a,s} for which we are going to check QQ relation with Q[a,s] in the top left corner (smallest a,s)
FullYoungDiagram - is maximal possible domain of interest*)
FullYoungDiagram=Block[{mm},Flatten@Table[mm[a,s],{a,0,Length[\[Lambda]]-1},{s,0,\[Lambda][[a+1]]-1}]/.mm->List];
DomainOfInterest=FullYoungDiagram;
(* comment below provides some example of non-standard DomainOfInterest *)
(*DomainOfInterest=Block[{mm},Flatten@Table[mm[a,s],{a,0,1},{s,0,1}]/.mm\[Rule]List];*)

Csystem[\[Lambda]];

Bsystem[\[Lambda]];

CcoeffAt\[CapitalLambda][theta_,sol_]:=Block[{},ccoeffattarget=c2bcoeffBos/.sol;
eqsrel=Allrel/.ccoeffattarget/.sym[n_]:>If[n==1,-\[CapitalLambda],0]/.\[CapitalLambda]->theta;
eqsrelred=Select[(eqsrel//Chop),!(#===0)&];
If[(eqsrelred//Length)>0,ccoeffsolvedattarget=FindMinimum[eqsrel . eqsrel,Variables[eqsrel]][[2]];
AppendTo[ccoeffattarget,ccoeffsolvedattarget]//Flatten,ccoeffattarget]];

)
];


(* ::Input:: *)
(*ClearAll[*)
(*  Fsym, MM, YQa, YQ\[Theta], QQrel, YQprod, coeff2root, rootsfromcoeff,*)
(*  Bdegs, Bbos, Bferm, Wron, Csystem, Bsystem, GenerateQsystemW,*)
(*  CcoeffAt\[CapitalLambda],*)
(*  Allrel, vars, vars2, FullYoungDiagram, DomainOfInterest,*)
(*  b2ccoeff, BcoeffWronskian, AllrelWronskian, bvars,*)
(*  c2bcoeffBos, wron, Len, J, H, dddf, fdot,*)
(*  x, q\[Theta], c, sym, b, MM, u, \[CapitalLambda]*)
(*]*)
(**)


(* ::Subsection:: *)
(*GetData*)


(* Function: GetBData at lambda=0 from Julia, Input SYT*)
GetBData[syt_List] := Module[
  {
   file,data, toIndexed, myvars, rules
  },
  
  (* --- Construct file path --- *)
  file = StringTemplate[
    ""<>ToString[SetDirectory[NotebookDirectory[]]]<>"/saved_data/result_`1`.csv"
  ][syt // ToString];
  
  (* --- Import and parse data --- *)
  data = Quiet@Check[
    Import[file] // Rest // ToExpression,
    Return[$Failed, Module]
  ];
  
  (* --- Convert b10 \[RightArrow] b[1,0] --- *)
  toIndexed[s_Symbol] := Module[{name, digits},
    name = SymbolName[s];
    digits = StringReplace[name, LetterCharacter .. -> ""];
    b @@ ToExpression /@ Characters[digits]
  ];
  
  (* --- Extract variables and rules --- *)
  myvars = toIndexed /@ data[[All, 1]];
  rules = Thread[myvars -> data[[All, 2]]];
  
  (* --- Return substitution rules --- *)
  rules
]



GetRootsFromSYT[syt_] := Module[
  {
    yd, Cdata, QpolyDomainOfInterest, allrootsDomainOfInterest
  },
  
  (* Convert SYT \[RightArrow] Young diagram *)
  yd = ToYD[syt];
  
  (* Generate Wronskian Q-system data *)
  GenerateQsystemW[yd];
  
  (* Get Bethe data for this tableau *)
  Cdata = CcoeffAt\[CapitalLambda][0, GetBData[syt]];
  
  (* Evaluate Q-polynomials at DomainOfInterest *)
  QpolyDomainOfInterest = Table[
    YQa[a, 0, yd] /. Cdata,
    {a, 1, Length@yd-1}
  ];
  
  (* Solve for all roots of each Q-polynomial *)
  allrootsDomainOfInterest = (u /. NSolve[# == 0, u]) & /@ QpolyDomainOfInterest;
  
  (* Return roots *)
  allrootsDomainOfInterest
]


GetAllRootsFromSYT[syt_] := Module[
  {
    yd, Cdata, QpolyDomainOfInterest, allrootsDomainOfInterest
  },
  
  (* Convert SYT \[RightArrow] Young diagram *)
  yd = ToYD[syt];
  
  (* Generate Wronskian Q-system data *)
  GenerateQsystemW[yd];
  
  (* Get Bethe data for this tableau *)
  Cdata = CcoeffAt\[CapitalLambda][0, GetBData[syt]];
  
  (* Evaluate Q-polynomials at DomainOfInterest *)
  QpolyDomainOfInterest = Table[
    YQa[DomainOfInterest[[a, 1]], DomainOfInterest[[a, 2]], yd] /. Cdata,
    {a, 2, Length@DomainOfInterest}
  ];
  
  (* Solve for all roots of each Q-polynomial *)
  allrootsDomainOfInterest = (u /. NSolve[# == 0, u]) & /@ QpolyDomainOfInterest;
  
  (* Return roots *)
  allrootsDomainOfInterest
]

ClearAll[GetAllRootsFromSYT];
GetAllRootsFromSYT[syt_] := Module[
  {
    yd, Cdata, QpolyDomainOfInterest, allrootsDomainOfInterest,
    res
  },
  
  Quiet@Module[
    {
      domainOk, coeffOk, solveOk
    },
    
    (* Step 1: convert SYT \[RightArrow] Young diagram *)
    yd = Check[ToYD[syt], $Failed];
    If[yd === $Failed,
      Print[" Failed: ToYD conversion for ", syt]; 
      Return[$Failed];
    ];
    
    (* Step 2: generate Wronskian Q-system *)
    If[FailureQ@Check[GenerateQsystemW[yd], $Failed],
      Print[" Failed: GenerateQsystemW for YD = ", yd];
      Return[$Failed];
    ];
    
    (* Step 3: check DomainOfInterest existence *)
    domainOk = TrueQ[ListQ[DomainOfInterest] && Length@DomainOfInterest > 1];
    If[!domainOk,
      Print[" DomainOfInterest not defined or empty after GenerateQsystemW"];
      Return[$Failed];
    ];
    
    (* Step 4: get coefficient data *)
    coeffOk = Check[Cdata = CcoeffAt\[CapitalLambda][0, GetBData[syt]], $Failed];
    If[coeffOk === $Failed,
      Print[" Failed: CcoeffAt\[CapitalLambda] or GetBData for ", syt];
      Return[$Failed];
    ];
    
    (* Step 5: build Q-polynomials *)
    QpolyDomainOfInterest = Check[
      Table[
        YQa[DomainOfInterest[[a, 1]], DomainOfInterest[[a, 2]], yd] /. Cdata,
        {a, 2, Length@DomainOfInterest}
      ],
      $Failed
    ];
    If[QpolyDomainOfInterest === $Failed || !VectorQ[QpolyDomainOfInterest],
      Print[" Failed: Could not construct Q-polynomials for ", syt];
      Return[$Failed];
    ];
    
    (* Step 6: solve for roots safely *)
    solveOk = Check[
      allrootsDomainOfInterest = (u /. NSolve[# == 0, u]) & /@ QpolyDomainOfInterest;
      allrootsDomainOfInterest,
      $Failed
    ];
    
    If[solveOk === $Failed || !ListQ[solveOk],
      Print[" NSolve failed for some Q-polynomials in ", syt];
      Return[$Failed];
    ];
    
    (* Step 7: return roots *)
    solveOk
  ]
];




(* ::Section::Closed:: *)
(*ShowPlots.nb*)


ClearAll[LoadBAEResults];
(*load bethe roots*)
LoadBAEResults[yd_,list_:All] := Module[
  {
    L, dataRoots, datamodes, databethe, datastring,
    datariggeds, dataStringtype,dataSYT
  },
  
  (* System size *)
  L = Total[yd];
  
  (* File path *)
  file = StringJoin[
    "/home/zuxian/Documents/BAE/RootsData/",
    ToString[yd], ".csv"
  ];
  
  (* Import and process data *)
  dataRoots = (Import[file] // ToExpression)[[list]];
  datamodes = dataRoots[[All, 1]];
  databethe = First /@ dataRoots[[All, 2]];
  datastring = dataRoots[[All, 3]];
  
  (* Construct rigged configurations *)
  datariggeds = ModestoRiggedConfig[L, #] & /@ datamodes;
  dataStringtype = datariggeds[[All, 2]];
  dataSYT= ToSYT/@datariggeds;
  
  <|
    "SystemSize" -> L,
    "File" -> file,
    "DataRoots" -> dataRoots,
    "DataModes" -> datamodes,
    "DataBethe" -> databethe,
    "DataString" -> datastring,
    "DataRiggeds" -> datariggeds,
    "DataStringType" -> dataStringtype,
    "DataSYT" -> dataSYT
  |>
]


ClearAll[LoadDistanceData];
(*load distance data*)
LoadDistanceData[yd_] := Module[
  {},
  
  files = FileNames[
    "distancedata_*.csv",
    "/home/zuxian/Documents/BAE_algorithm/final_result/distance_" <> ToString[yd]
  ];
  
  dataKKR = (Import[#, "CSV"] & /@ files) // ToExpression;
  
]


PlotDistanceBoxWhisker[dataKKR_, indexa_,length_] := Module[
  {
    listofdistance = 6,
    listofdiffdistance = 4,
    listofkkr = 2
  },
  
  Show[
    BoxWhiskerChart[
      dataKKR[[All, indexa]][[All, listofdistance]],
        ChartLabels ->  Table[
        (* Only show label every 10th point *)
        If[Mod[i, 10] == 0, i, ""],
        {i, Length[dataKKR[[1 ;; -1,myindexa]][[All, 6]]]}
      ],AspectRatio->1/3
    ],
    Graphics[
      Transpose[{
        Thread[
          If[
            Thread[dataKKR[[All, indexa]][[All, listofdiffdistance]] == 0],
            Blue, Red
          ]
        ],
        ConstantArray[PointSize[Large], Length[dataKKR]],
        Table[
          Point[{kk, dataKKR[[All, indexa]][[All, listofkkr]][[kk]]}],
          {kk, Length[dataKKR]}
        ]
      }]
    ]
  ]
]



PlotBetheVsString[yd_, index_] := (
  With[{a = #},
    ComplexListPlot[
      {
        Callout[#, #, Above, LeaderSize -> 10] & /@ 
          N@Round[databethe[[index, a]], 10^-3],
        Callout[#, #, Below, LeaderSize -> 10] & /@ 
          N@Round[datastring[[index, a]], 10^-3]
      },
      PlotMarkers -> {
        {"\[FilledUpTriangle]", 15},
        {"\[FilledSquare]", 15}
      },
      PlotLegends -> {
        "Exact Bethe root",
        "String root"
      },
      PlotRange -> All, 
      AxesLabel -> {"Re u", "Im u"}, 
      Frame -> True, 
      ImageSize -> 700, 
      AspectRatio -> 1/2, 
      ImageMargins -> 0, 
      ImagePadding -> 0
    ]
  ] & /@ Range[Length[yd] - 1]
)


PlotDistanceBoxWhisker[dataKKR_, indexa_, length_] := Module[
    {
       listofdistance = 6,
       listofdiffdistance = 4,
       listofkkr = 2
     },
    
    Show[
       BoxWhiskerChart[
          dataKKR[[1 ;; length, indexa]][[All, listofdistance]],
          ChartLabels -> Table[
            (* Only show label every 10th point *)
            If[Mod[i, 10] == 0, i, ""],
            {i, Length[dataKKR[[1 ;; length, indexa]][[All, listofdistance]]]}
          ]
        ],
       Graphics[
          Transpose[{
              Thread[
                 If[
                   Thread[dataKKR[[1 ;; length, indexa]][[All, listofdiffdistance]] == 0],
                   Blue, 
                   Red
                 ]
               ],
              ConstantArray[PointSize[Large], length],
              Table[
                Point[{kk, dataKKR[[1 ;; length, indexa]][[All, listofkkr]][[kk]]}],
                {kk, length}
              ]
            }]
        ]
     ]
  ]


(* ::Section:: *)
(*HelpFunctionInStringSolver*)


(*Input: Modes number and it length. Output: string roots*)
SolutionFromModeConfigurationSafe[modes_,L_]:=Check[
       TimeConstrained[
         Quiet[
           SolutionFromModeConfiguration[modes, L] // Chop,
           {FrontEndObject::notavail, FindRoot::bddir}
         ],
         40,
         StringSolver[modes, L]
       ],
       StringSolver[modes, L]
     ] // Quiet


ClearAll[GetAllStringConfig];
(*Input: syt. Output: all possible string configurations*)
GetAllStringConfig[syt_] := Module[
  {yd, rigged},
  
  (* Young diagram from SYT *)
  yd = ToYD[syt];
  
  (* Rigged configuration corresponding to the SYT *)
  rigged = ToRiggedExact[syt];
  
  (* Generate the list of modes *)
  RigsForStringConfigSorted[yd, rigged[[2]]]
]

ClearAll[GetAllStringSol];
(*Input: syt. Output: all possible solutions of string configurations*)
GetAllStringSol[syt_] := Module[
  {yd, rigged, listofmode, maxnum},
  
  yd = ToYD[syt];
  rigged = ToRiggedExact[syt];
  
  (* Compute list of mode configurations *)
  listofmode = RiggedToModes /@ RigsForStringConfigSorted[yd, rigged[[2]]];
  
  (* Determine the maximum label in the SYT *)
  maxnum = Max@Flatten[syt];
  
  (* Compute the safe solution for each mode configuration *)
  ParallelTable[
    SolutionFromModeConfigurationSafe[listofmode[[kk]], maxnum],
    {kk, Length@listofmode}
  ]
]


GetStringSol[syt_] := Module[
  {yd, rigged, listofmode, maxnum},
  
  rigged = ToRiggedExact[syt];
  
  (* Determine the maximum label in the SYT *)
  maxnum = Max@Flatten[syt];
  
  (* Compute the safe solution for each mode configuration *)
   SolutionFromModeConfigurationSafe[RiggedToModes@rigged, maxnum]
]



(* ::Section::Closed:: *)
(*HelpFunctionInPlot*)


ClearAll[PlotFlipDistance];
PlotFlipDistance[result_,syt_] := Module[
  {
    pos1, pos2, result1, result2, dist
  },
  
  (* Find position of original SYT *)
  pos1 = FirstPosition[result[["DataSYT"]], syt, Missing["NotFound"]];
  If[pos1 === Missing["NotFound"], 
    Return["SYT not found in result data."]];
  
  (* Get Bethe roots for original *)
  result1 = result[["DataBethe"]][[pos1[[1]]]];
  
  (* Find position of flipped SYT *)
  pos2 = FirstPosition[
    result[["DataSYT"]],
    ToSYT @ FlipConfig @ ToRigged @ syt,
    Missing["NotFound"]
  ];
  If[pos2 === Missing["NotFound"],
    Return["Flipped configuration not found."]];
  
  (* Get Bethe roots for flipped *)
  result2 = result[["DataBethe"]][[pos2[[1]]]];
  
  (* Compute distance *)
  dist = DistanceMeasure[Flatten[result1], -Flatten[result2]];
  
  (* Plot both sets on complex plane *)
  ComplexListPlot[
    {Flatten[result1], -Flatten[result2]},
    PlotStyle -> {Blue, Red},
    PlotLegends -> {"Original", "Flipped"},
    PlotLabel -> 
      StringJoin[
        "Distance = ", ToString[dist, InputForm]
      ],
    AxesLabel -> {"Re", "Im"},
    AspectRatio -> 1,
    ImageSize -> Large,
    Frame->True,
    PlotRange->All
  ]
];


ClearAll[PlotTransposeDistance];
PlotTransposeDistance[syt_] := Module[
  {result1, result2, dist},
  
  (* Compute Bethe roots for SYT and its transpose *)
  result1 = GetAllRootsFromSYT[syt];
  result2 = GetAllRootsFromSYT[TransposeSYT[syt]];
  
  (* Compute distance *)
  dist = DistanceMeasure[Flatten[result1], Flatten[result2]];
  
  (* Plot both sets in the complex plane *)
  ComplexListPlot[
    {Flatten[result1], Flatten[result2]},
    PlotStyle -> {Blue, Red},
    PlotLegends -> {"Original SYT", "Transposed SYT"},
    PlotLabel -> 
      StringJoin[
        "Distance = ", ToString[dist, InputForm]
      ],
    AxesLabel -> {"Re", "Im"},
    AspectRatio -> 1,
    ImageSize -> Large,
    Frame->True,
    PlotRange->All
  ]
];



ClearAll[PlotStringVsBethe];
PlotStringVsBethe[result_,syt_] := Module[
  {pos, re1, re2, yd, numLevels, plots},
  
  (* Step 1: find the SYT position in the dataset *)
  pos = FirstPosition[result["DataSYT"], syt, Missing["NotFound"]];
  If[pos === Missing["NotFound"],
    Print[" SYT not found in result data."];
    Return[$Failed];
  ];
  pos = First[pos];
  
  (* Step 2: extract string and Bethe data *)
  re1 = result["DataString"][[pos]];
  re2 = result["DataBethe"][[pos]];
  
  (* Step 3: determine number of Q-levels (rank-1 per row of YD) *)
  yd = ToYD[syt];
  numLevels = Length[yd] - 1;
  
  (* Step 4: generate plots for each level *)
  plots = Table[
    Module[{dist},
      dist = DistanceMeasure[re1[[kk]], re2[[kk]]];
      ComplexListPlot[
        {re1[[kk]], re2[[kk]]},
        PlotStyle -> {Blue, Red},
        PlotLegends -> {"String roots", "Bethe roots"},
        PlotLabel -> 
          StringJoin[
            "Level ", ToString[kk],
            "  |  Distance = ", ToString[dist, InputForm]
          ],
        AspectRatio -> 1,
        Frame -> True,
        ImageSize -> 300
      ]
    ],
    {kk, numLevels}
  ];
  
  (* Step 5: return the grid of plots *)
  Grid[
    Partition[plots, UpTo[3]],
    Spacings -> {0.0, 0.0},
    Frame -> None
  ]
];


(* ::Section::Closed:: *)
(*OldFunctionsNoNeed*)


(* ::Input:: *)
(*DistanceMeasure[a_,b_] := Module[*)
(*  {n, perms, costs, minCost, bestPerm,costMatrix},*)
(*costMatrix=DistanceMatrix[a,b];*)
(*  n = Length[costMatrix];*)
(*  perms = Permutations[Range[n]];*)
(*  costs = Total[Extract[costMatrix, Thread[{Range[n], #}]]] & /@ perms;*)
(*  minCost = Min[costs];*)
(*  bestPerm = perms[[First@FirstPosition[costs, minCost]]];*)
(*  {minCost, Thread[Range[n] -> bestPerm]};*)
(*minCost*)
(*]*)
(**)
(*DistanceMeasure[a_,b_]:=Module[{dmatrix,mins,total},*)
(*dmatrix =DistanceMatrix[a,b];*)
(*mins=Min/@dmatrix;*)
(*     total=Mean[mins];*)
(*total*)
(*]*)
(**)
(*ClearAll[HungarianMinCostAssignment]*)
(*HungarianMinCostAssignment::nonsquare = "Cost matrix must be square.";*)
(**)
(*HungarianMinCostAssignment[cost_?MatrixQ, tol_: 10^-10] := Module[*)
(*  {*)
(*    n, orig, a, starred, primed, coverRow, coverCol,*)
(*    colsToCover, zeros, r, c, posStarInRow, rowsUncov, colsCov, vals, h,*)
(*    path, rowStarPos, colPrimePos, positionsStar, minCost, assignment*)
(*  },*)
(*  *)
(*  If[Apply[Equal, Dimensions[cost]] === False, Message[HungarianMinCostAssignment::nonsquare]; Return[$Failed]];*)
(*  *)
(*  n = Length[cost];*)
(*  orig = N[cost];                 (* keep original for final cost *)*)
(*  a = orig;*)
(*  *)
(*  (* 1) Row & column reductions *)*)
(*  a = a - Min /@ a;*)
(*  a = Transpose[Transpose[a] - Min /@ Transpose[a]];*)
(*  *)
(*  (* State *)*)
(*  starred = ConstantArray[False, {n, n}];*)
(*  primed  = ConstantArray[False, {n, n}];*)
(*  coverRow = ConstantArray[False, n];*)
(*  coverCol = ConstantArray[False, n];*)
(*  *)
(*  (* 2) Star a maximal set of independent zeros (greedy) *)*)
(*  Do[*)
(*    Do[*)
(*      If[Abs[a[[i, j]]] <= tol && !AnyTrue[starred[[i, All]], TrueQ] && !AnyTrue[starred[[All, j]], TrueQ],*)
(*        starred[[i, j]] = True;*)
(*      ],*)
(*      {j, 1, n}*)
(*    ],*)
(*    {i, 1, n}*)
(*  ];*)
(*  *)
(*  (* Cover columns containing a starred zero *)*)
(*  colsToCover = Select[Range[n], AnyTrue[starred[[All, #]], TrueQ] &];*)
(*  coverCol[[colsToCover]] = True;*)
(*  *)
(*  While[Count[coverCol, True] < n,*)
(*    (* Find an uncovered zero and prime it. If none, adjust matrix. *)*)
(*    zeros = Select[*)
(*      Position[a, _?(Abs[#] <= tol &)],*)
(*      (!coverRow[[#[[1]]]] && !coverCol[[#[[2]]]]) &*)
(*    ];*)
(*    *)
(*    If[zeros === {},*)
(*      (* 3) Adjust matrix by the smallest uncovered value *)*)
(*      rowsUncov = Flatten@Position[coverRow, False];*)
(*      colsCov   = Flatten@Position[coverCol, True];*)
(*      vals = Flatten@Table[a[[ii, jj]], {ii, rowsUncov}, {jj, Complement[Range[n], colsCov]}];*)
(*      h = Min@Select[vals, # > tol &];*)
(*      If[rowsUncov =!= {}, a[[rowsUncov, All]] -= h];*)
(*      If[colsCov   =!= {}, a[[All, colsCov]]   += h];*)
(*      Continue[];*)
(*    ];*)
(*    *)
(*    {r, c} = First@zeros;*)
(*    primed[[r, c]] = True;*)
(*    posStarInRow = Position[starred[[r, All]], True];*)
(*    *)
(*    If[posStarInRow === {},*)
(*      (* 4) Augmenting path: start at this primed zero *)*)
(*      path = {{r, c}};*)
(*      Module[{rr = r, cc = c},*)
(*        While[True,*)
(*          (* Starred zero in this column? *)*)
(*          rowStarPos = Position[starred[[All, cc]], True];*)
(*          If[rowStarPos === {}, Break[]];*)
(*          rr = First@First@rowStarPos;*)
(*          AppendTo[path, {rr, cc}];*)
(*          (* Primed zero in this row (must exist) *)*)
(*          colPrimePos = Position[primed[[rr, All]], True];*)
(*          cc = First@First@colPrimePos;*)
(*          AppendTo[path, {rr, cc}];*)
(*        ];*)
(*      ];*)
(*      (* Flip stars along the path; clear primes; uncover all *)*)
(*      Do[*)
(*        If[starred[[Sequence @@ pt]], starred[[Sequence @@ pt]] = False, starred[[Sequence @@ pt]] = True],*)
(*        {pt, path}*)
(*      ];*)
(*      primed  = ConstantArray[False, {n, n}];*)
(*      coverRow = ConstantArray[False, n];*)
(*      coverCol = ConstantArray[False, n];*)
(*      colsToCover = Select[Range[n], AnyTrue[starred[[All, #]], TrueQ] &];*)
(*      coverCol[[colsToCover]] = True;*)
(*      ,*)
(*      (* Else: there is a starred zero in the row \[RightArrow] cover row, uncover that starred column *)*)
(*      coverRow[[r]] = True;*)
(*      coverCol[[First@First@posStarInRow]] = False;*)
(*    ];*)
(*  ];*)
(*  *)
(*  positionsStar = Position[starred, True];*)
(*  minCost = Total@Extract[orig, positionsStar];*)
(*  assignment = Thread[Range[n] -> positionsStar[[All, 2]]];*)
(*  {minCost, assignment};*)
(*minCost*)
(*]*)
(**)
(**)
(**)
(**)
