(* ::Package:: *)

(* TYPE D RECTANGULAR RIGGED CONFIGURATION RELATED FUNCTIONS *)
(* Version 10/Sep/2013 *)

(* Tensor product is the Kashiwara convention *)
(* Coded by Reiho Sakamoto [Sep/2010] & [Jan/2011] & [Sep/2013] *)

(* kkrrec[rec, conf] produces tensor products specified by
the sequence of rectangles "rec" and the rest of the RC "conf" *)
(* Example;
In[1]:=kkrrec[{{2,2},{1,4},{3,1},{4,4},{2,3},{4,3},{5,2},{3,3}},
{{{2},{3,2,1},{2,2,1,1},{2,2,1,1,1,1},{3,2,1,1,1,1},{2,1,1},{2,2}},
{{2},{1,0,0},{4,1,2,1},{1,0,0,0,0,0},{0,1,0,0,0,0},{0,0,0},{0,0}}}];
Out[1]=
{{{1,2},{1,2}},{{1},{1},{1},{1}},{{1,2,3}},
{{1,2,3,4},{1,2,3,4},{1,3,4,5},{3,4,5,6}},
{{1,2},{1,2},{1,2}},{{1,2,3,4},{1,2,3,4},{2,3,7,-7}},
{{1,2,3,5,6},{1,2,3,-6,-5}},{{1,2,3},{1,3,4},{1,3,-5}}};
Try the following function on the output:
In[2]:=Map[Grid[Transpose[#],Frame->All]&,%] *)

(* rkkrec[path, rank] produces the rigged configuration of
 the "rank" corresponding to "path"*)
(*Example; tensor product of two rectangles;
In[3]:=rkkrec[{{{1,2},{1,2}},{{1},{1},{1},{1}},{{1,2,3}},
{{1,2,3,4},{1,2,3,4},{1,3,4,5},{3,4,5,6}},
{{1,2},{1,2},{1,2}},{{1,2,3,4},{1,2,3,4},{2,3,7,-7}},
{{1,2,3,5,6},{1,2,3,-6,-5}},{{1,2,3},{1,3,4},{1,3,-5}}},7]
Out[3]={{{4},{2,3},{1,3},{4,3},{2}},
{{2},{3,2,1},{2,2,1,1},{2,2,1,1,1,1},{3,2,1,1,1,1},{2,1,1},{2,2}},
{{2},{1,0,0},{4,1,2,1},{1,0,0,0,0,0},{0,1,0,0,0,0},{0,0,0},{0,0}}}*)


(* Utility functions *)
(* vac[rc,a,l] gives Subscript[Q^(a),l] for rigged configuration *)
vac[rc_, a_, l_] := Module[{nrc},
  nrc = ReplacePart[rc, 
    1 -> Join[rc[[1]] /. {} -> {0}, 
      Table[{0}, {Max[0, Length[rc[[2]] ] - Length[rc[[1]] ]]}] ] ];
  
  Which[Length[nrc[[2]]] == 3 && a == 1, 
   Total[Map[Min[l, #] &, nrc[[1, 1]]]] - 
    2 Total[Map[Min[l, #] &, nrc[[2, 1]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, 2]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, 3]]]],
   
   a == 1, 
   Total[Map[Min[l, #] &, nrc[[1, a]]]] - 
    2 Total[Map[Min[l, #] &, nrc[[2, a]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, a + 1]]]],
   
   a < Length[nrc[[2]]] - 2, 
   Total[Map[Min[l, #] &, nrc[[1, a]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, a - 1]]]] - 
    2 Total[Map[Min[l, #] &, nrc[[2, a]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, a + 1]]]],
   
   a == Length[nrc[[2]]] - 2, 
   Total[Map[Min[l, #] &, nrc[[1, a]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, a - 1]]]] - 
    2 Total[Map[Min[l, #] &, nrc[[2, a]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, a + 1]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, a + 2]]]],
   
   True, Total[Map[Min[l, #] &, nrc[[1, a]]]] + 
    Total[Map[Min[l, #] &, nrc[[2, Length[rc[[2]]] - 2]]]] - 
    2 Total[Map[Min[l, #] &, nrc[[2, a]]]]]  ]

(* rcnorder[rc] gives normal ordered RC;
Lengths of rows->decreasing,
riggings->decreasing within the rows of same length *)
rcnorder[rc_] := 
 Module[{comb, ans = rc, i}, 
  For[i = 1, i <= Length[rc[[2]]], i++, 
   comb = Reverse[
     Sort[Table[{rc[[2, i, j]], rc[[3, i, j]]}, {j, 1, 
        Length[rc[[2, i]]]}]]];
   ans = ReplacePart[ans, {2, i} -> Map[#[[1]] &, comb]];
   ans = ReplacePart[ans, {3, i} -> Map[#[[2]] &, comb]]]; ans]


(* KKR:RC->Path functions *)
(* For RC->Path map, kkrsing[rc,a,l,taken] gives position of the
rightmost singular element of mu^a longer than or equal to l;
We do not choose a row specified by the position "taken";
If there is no such string,return {} *)
kkrsing[rc_, a_, l_, taken___] := 
 Module[{vacancy, vaclist, candidate}, 
  vacancy = 
   Map[{#, vac[rc, a, #]} &, 
    Select[Reverse[Union[rc[[2, a]]]], # >= l &]];
  vaclist = 
   Flatten[Table[
     Table[vacancy[[i, 2]], {Count[rc[[2, a]], vacancy[[i, 1]]]}], {i,
       1, Length[vacancy]}]];
  candidate = 
   Select[Position[
     Table[vaclist[[i]] == rc[[3, a, i]], {i, 1, Length[vaclist]}], 
     True], #[[1]] < taken &];
  If[candidate == {}, {}, {Max[candidate]}]]

(* kkrchoosesing[rc,a,start] gives position of rows to be removed,
starting from length "start" row of nu^(a-1) *)
kkrchoosesing[rc_, a_, start_] := 
 Module[{ans = Table[{}, {a - 1}], prev = start, i}, 
  For[i = a, i <= Length[rc[[2]]] - 2, i++, 
   ans = Append[ans, kkrsing[rc, i, prev]];
   If[ans[[-1]] == {}, Return[Drop[ans, -1]]];
   prev = rc[[2, i, ans[[-1, 1]]]]];
  ans = Join[
    ans, {kkrsing[rc, Length[rc[[2]]] - 1, prev]}, {kkrsing[rc, 
      Length[rc[[2]]], prev]}];
  If[ans[[-1]] == {} && ans[[-2]] == {}, 
   Return[Delete[ans, {{-1}, {-2}}]]];
  If[ans[[-1]] == {} || ans[[-2]] == {}, Return[ans]];
  prev = Max[rc[[2, -1, ans[[-1, 1]]]], rc[[2, -2, ans[[-2, 1]]]]];
  For[i = Length[rc[[2]]] - 2, i >= 1, i--,
   ans = If[ans[[i]] == {},
     Append[ans, kkrsing[rc, i, prev]],
     Append[ans, kkrsing[rc, i, prev, ans[[i, 1]] ]]];
   If[ans[[-1]] == {}, Return[Drop[ans, -1]]];
   prev = rc[[2, i, ans[[-1, 1]]]]]; ans]

(* kkrdelta[rc,a,start] gives one step removal from
nu^(a-1);output={removed RC,output letter},starting from the
rightmost box of the quantum space specified by start *)
kkrdelta[rc_, a_, start_] := 
 Module[{data, ans, i, rank = Length[rc[[2]]], nullstr, letter}, 
  ans = rcnorder[rc]; data = kkrchoosesing[ans, a, start];
  (*for empty RC--4 types*)
  If[a == 1 && Flatten[rc[[2]]] == {} && rc[[1, a, -1]] == 1,
   Return[{{ReplacePart[rc[[1]], 1 -> Delete[rc[[1, 1]], -1]],
      Table[{}, {rank}], Table[{}, {rank}]}, 1}]];
If[a == 1 && Flatten[rc[[2]]] == {} ,
Return[{{ReplacePart[rc[[1]], 1 ->MapAt[(#-1)&,rc[[1,1]],-1] ],
 Table[{}, {rank}], Table[{}, {rank}]}, 1}]];
If[Flatten[rc[[2]]] == {} && rc[[1, a, -1]] == 1,
   Return[{{ReplacePart[rc[[1]], {(a - 1) -> Append[rc[[1, a - 1]], 1],
        a -> Delete[rc[[1, a]], -1]}],
      Table[{}, {rank}], Table[{}, {rank}]}, a}]];
  If[Flatten[rc[[2]]] == {},
 Return[{{ReplacePart[
       rc[[1]], {(a - 1) -> Append[rc[[1, a - 1]], 1], 
        a -> MapAt[(# - 1) &, rc[[1, a]], -1]}], Table[{}, {rank}], 
      Table[{}, {rank}]}, a}]];
  (*remove one box from configurations*)
  For[i = 1, i <= Min[rank, Length[data]], i++, 
   ans = If[data[[i]] == {}, ans, 
     MapAt[(# - 1) &, ans, {2, i, data[[i, 1]]}]]];
  If[Length[data] > rank, 
   For[i = 1, i <= Length[data] - rank, i++, 
    ans = MapAt[(# - 1) &, 
      ans, {2, rank - 1 - i, data[[rank + i, 1]]}]]];
  (*remove quantum space*)
  ans = If[start == 1, Delete[ans, {1, a, -1}], 
    MapAt[(# - 1) &, ans, {1, a, -1}]];
  ans = If[a > 1, Insert[ans, 1, {1, a - 1, -1}], ans];
  (*change riggings*)
  For[i = 1, i <= Min[rank, Length[data]], i++, 
   ans = If[data[[i]] == {}, ans, 
     ReplacePart[
      ans, {3, i, data[[i, 1]]} -> 
       vac[ans, i, ans[[2, i, data[[i, 1]]]]]]]];
  If[Length[data] > rank, 
   For[i = 1, i <= Length[data] - rank, i++, 
    ans = ReplacePart[
      ans, {3, rank - 1 - i, data[[rank + i, 1]]} -> 
       vac[ans, rank - 1 - i, 
        ans[[2, rank - 1 - i, 
          data[[rank + i, 1]]]]]]]];(*determine the output letter*)
  letter = Which[Length[data] == 0, 1, Length[data] < rank, 
    Length[data] + 1, 
    Length[data] == rank && data[[rank - 1]] == {}, -rank, 
    Length[data] == rank && data[[rank]] == {}, rank, 
    Length[data] == rank, -(rank - 1), 
    True, -(2 rank - Length[data] - 1)];
  If[Union[Flatten[ans[[2]]]] == {0}, 
   Return[{{ans[[1]], Table[{}, {rank}], Table[{}, {rank}]}, letter}]];
  nullstr = Position[ans[[2]], 0];
  (*remove length zero strings*)
  If[nullstr == {}, Return[{ans, letter}]];
  For[i = Length[nullstr], i >= 1, i--, 
   ans = Delete[
     ans, {Prepend[nullstr[[i]], 2], Prepend[nullstr[[i]], 3]}]];
  {ans, letter}]

(* kkr main functions *)
kkronecol[rc_, a_] := Module[{med, lett, i},
  med = kkrdelta[rc, a, rc[[1, a, -1]] ];
  lett = {med[[2]]};
  For[i = a - 1, i >= 1, i--,
   med = kkrdelta[med[[1]], i, 1];
   lett = Prepend[lett, med[[2]]] ];
  {med[[1]], lett}]

kkronerec[rc_, a_] := Module[{med = {rc, Pi}, rec = {}, i},
  For[i = 1, i <= rc[[1, a, -1]], i++,
   med = kkronecol[med[[1]], a];
   rec = Append[rec, med[[2]] ] ];
  {med[[1]], rec}]

kkrrec[rec_,rcrest_]:=Module[
{rc,qs,heights=Reverse[Map[#[[1]]&,rec]],i,ans={},aux},
qs=Table[{},{Max[heights]}];
For[i=1,i<=Length[rec],i++,
qs=MapAt[Append[#,rec[[i,2]] ]&,qs,rec[[i,1]] ](*For*)];
rc=Join[{qs},rcrest];
For[i=1,i<=Length[rec],i++,
aux=kkronerec[rc,heights[[i]] ];
rc=aux[[1]];ans=Prepend[ans,aux[[2]] ]
(*For*)];
ans]


(* RKK: Path -> RC functions *)
(* For Path -> RC map, rkksing[rc,a,l,added] gives position of the 
rightmost singular element of mu^a shorter than or equal to l; We do 
not choose a row specified by the position "added"; If there is no 
such string, return {0}*)
rkksing[rc_, a_, l_, added___] := Module[{data, vaclist, candidate},
    data = 
   Map[{#, vac[rc, a, #]} &, 
    Select[Reverse[Union[rc[[2, a]]]], # <= l &]];
    vaclist = Flatten[Table[ Table[data[[i, 2]],
       {Count[rc[[2, a]], data[[i, 1]]]}], {i, 1, Length[data]}]];
  (* rename symbol data = relevant part of the riggings *)
    data = Take[rc[[3, a]], -Length[vaclist]];
    candidate = 
   Select[Position[ 
     Table[vaclist[[i]] == data[[i]], {i, 1, Length[vaclist]}],  True],
     #[[1]] > (added - Length[rc[[3, a]] ] + Length[data]) &];
    If[candidate == {}, {0}, {Min[candidate] + 
     Length[rc[[3, a]] ] -   Length[data]}]]

(* rkkchoosesing[rc,a,letter] gives the sequence of positions to be 
added a box; {0} means creating a new row;
the sequence proceeds from the configuration specified by 
"letter",...,-rank-1,-rank,-rank-2,...,1;
left a elements are {} since it will terminate at nu^a;
If letter = -rank, we should ignore "-2"st Young diagram which is 
expressed by {} *)
rkkchoosesing[rc_, a_, letter_] := Which[
    letter > 0, Module[{ans = {}, prev = Infinity, i},
      For[i = letter - 1, i > a, i--,
        ans = Prepend[ans, rkksing[rc, i, prev]];
        prev = rc[[2, i, ans[[1, 1]] ]](*For*)]; 
   Join[ Table[{}, {a}], ans]],
    
    letter > -Length[rc[[2]] ] + 1, 
    Module[{ans = {}, i, prev = Infinity},
      For[i = -letter, i <= Length[rc[[2]] ] - 2, i++,
        ans = Prepend[ans, rkksing[rc, i, prev]];
        prev = rc[[2, i, ans[[1, 1]] ]] ];
      ans = Prepend[ans, rkksing[rc, Length[rc[[2]] ], prev]];
      ans = Prepend[ans, rkksing[rc, Length[rc[[2]] ] - 1, prev]];
      prev = If[ans[[1]] == {0} && ans[[2]] == {0}, 0,
          Min[rc[[2, Length[rc[[2]] ], ans[[2, 1]] ]],
            rc[[2, Length[rc[[2]] ] - 1, ans[[1, 1]] ]] ](*If*)];
      For[i = Length[rc[[2]] ] - 2, i > a, i--,
        ans = Which[i < -letter, Prepend[ans, rkksing[rc, i, prev]],
            ans[[-(i + letter + 1)]] == {0}, Prepend[ans, {0}],
            True, 
            Prepend[ans, 
              
       rkksing[rc, i, prev, ans[[-(i + letter + 1), 1]]  ] ](*Which*)];
        prev = Which[i < -letter, rc[[2, i, ans[[1, 1]] ]],
            ans[[-(i + letter + 1)]] == {0}, 0,
            True, rc[[2, i, ans[[1, 1]] ]](*Which*)]
        (*For*)]; Join[ Table[{}, {a}], ans]],
    
    letter == -Length[rc[[2]] ] + 1, 
    Module[{ans = {}, prev = Infinity, i},
      ans = Prepend[ans, rkksing[rc, Length[rc[[2]] ], prev]];
      ans = Prepend[ans, rkksing[rc, Length[rc[[2]] ] - 1, prev]];
      prev = 
        Min[rc[[2, Length[rc[[2]] ] - 1, ans[[1, 1]] ]], 
          rc[[2, Length[rc[[2]] ], ans[[2, 1]] ]]  ];
      For[i = Length[rc[[2]] ] - 2, i > a, i--,
        ans = Prepend[ans, rkksing[rc, i, prev]];
        prev = rc[[2, i, ans[[1, 1]] ]](*For*)];
       Join[ Table[{}, {a}], ans]],
    
    True, Module[{ans = {}, prev, i},
      ans = {{}, rkksing[rc, -letter, Infinity]};
      prev = rc[[2, -letter, ans[[-1, 1]] ]];
      For[i = -letter - 2, i > a, i--,
        ans = Prepend[ans, rkksing[rc, i, prev]];
        prev = rc[[2, i, ans[[1, 1]] ]](*For*)];
    Join[ Table[{}, {a}], ans]]
    (*Which*)]

(* rkkdelta[rc,a,letter,start] gives the RC after one step box \
additions by the "letter" ending at "start"-th column of the row of \
nu^a of the quantum space *)
rkkdelta[rc_, a_, letter_, start_] := 
  Module[{ans = rc, data = rkkchoosesing[rc, a, letter], i, addbox, 
      changerig},
  (*change in the quantum space*)
  ans = Which[a < Length[ans[[1]] ] && start == 1, 
    MapAt[Append[#, 1] &, ans, {1, a + 1}],
    a < Length[ans[[1]] ], MapAt[(# + 1) &, ans, {1, a + 1, -1}],
    True, MapAt[Append[#, {1}] &, ans, 1]];
  ans = Which[a == 0, ans,
    ans[[1, a, -1]] == 1, MapAt[Most[#] &, ans, {1, a}],
    True, MapAt[(# - 1) &, ans, {1, a, -1}]];
  (*box addition*)
    addbox[conf_, pos_] := 
      Which[pos == {}, conf, conf == {}, {1}, pos[[1]] > 0, 
        MapAt[(# + 1) &, conf, pos[[1]]], True, Append[conf, 1]];
  (*rigging redefinition*)
    changerig[aa_, rig_, pos_] := 
      Which[pos == {}, rig, rig == {}, {vac[ans, aa, 1]},
        pos[[1]] > 0, 
        ReplacePart[rig, 
          pos[[1]] -> vac[ans, aa, ans[[2, aa, pos[[1]] ]] ] ],
        True, Append[rig, vac[ans, aa, 1] ]  ];
  (*change configuration*)
    ans = Which[letter > 0, 
        For[i = 1, i <= letter - 1, i++, 
          ans = MapAt[addbox[#, data[[i]] ] &, ans, {2, i}](*For*)]; 
    ans,
        letter == -Length[rc[[2]] ] || letter == -Length[rc[[2]] ] + 1,
        For[i = 1, i <= Length[rc[[2]] ], i++, 
          ans = MapAt[addbox[#, data[[i]] ] &, ans, {2, i}](*For*)];
        ans,
        True, 
        For[i = 1, i <= Length[rc[[2]] ], i++, 
          ans = MapAt[addbox[#, data[[i]] ] &, ans, {2, i}](*For*)];
        For[i = Length[rc[[2]] ] + 1, i <= Length[data], i++,
          ans = 
            MapAt[addbox[#, data[[i]] ] &, 
              ans, {2, 2 Length[rc[[2]] ] - i - 1}](*For*)]; 
    ans(*Which*)];
    (* Below, we will change riggings *)
    ans = Which[letter > 0,
        For[i = 1, i <= letter - 1, i++, 
          
     ans = MapAt[changerig[i, #, data[[i]] ] &, ans, {3, i}](*For*)]; 
        ans,
        letter == -Length[rc[[2]] ] || letter == -Length[rc[[2]] ] + 1,
        For[i = 1, i <= Length[rc[[2]] ], i++, 
          
     ans = MapAt[changerig[i, #, data[[i]] ] &, ans, {3, i}](*For*)]; 
        ans,
        True, 
        For[i = 1, i <= Length[rc[[2]] ], i++, 
          
     ans = MapAt[changerig[i, #, data[[i]] ] &, ans, {3, i}](*For*)];
        For[i = Length[rc[[2]] ] + 1, i <= Length[data], i++,
          ans = 
            
      MapAt[changerig[2 Length[rc[[2]] ] - i - 1, #, data[[i]] ] &, 
              ans, {3, 2 Length[rc[[2]] ] - i - 1}](*For*)]; 
    ans (*Which*)];
    rcnorder[ans]]

(* rkk main functions *)
rkkonecol[rc_, b_,s_] := Module[{ans = rc, i},
  For[i = 1, i < Length[b], i++,
   ans = rkkdelta[ans, i-1,b[[i]],1]];
rkkdelta[ans,Length[b]-1,b[[-1]],s]]

rkkonerec[rc_,rec_] := 
 Module[{ans = rc, i},
  For[i = Length[rec], i >= 1, i--,
   ans = rkkonecol[ans, rec[[i]],  Length[rec]-i+1]]; ans]

rkkrec[path_,rank_]:=Module[{ans={Table[{},{Max[Map[Length[#[[1]] ]&,path]]}],
Table[{},{rank}],Table[{},{rank}]},i},
For[i=1,i<=Length[path],i++,
ans=rkkonerec[ans,path[[i]] ](*For*)];
ans]


(* tabfill sends an element of the KR crystal "tab"
into r by s rectangular tableaux that corresponds
to the column splittings;
Example;
In[4]:=tabfill[{{1,2,3,4,5,6,7,8},{1,2,3,4},{1,2}},10,4]
Out[4]={{1,2,3,4,7,8,9,10,-10,-9},{1,2,7,8,9,10,-10,-9,-8,-7},
{5,6,7,8,9,10,-10,-9,-8,-7},{1,2,3,4,5,6,7,-7,-6,-5}}*)
tabfill[tab_,r_,s_]:=Module[
{vacleft,rectab,num,cri,f1,f2,f3,f4,middle,t,side,i},
(*remove vacuum columns and add {} for height 0 columns*)
vacleft=Select[tab,Length[#]==r&];
rectab=Drop[Join[tab,Table[{},{s-Length[tab]}]],Length[vacleft]];
(*num is number of columns of equal heights*)
num=Tally[Map[Length[#]&,rectab]];
(*filling functions for Step 1*)
f1[col_]:=Flatten[{col,Table[-j,{j,r,Length[col]+1,-1}]}];
f2[col_]:=Table[j,{j,1,r}];
(*filling functions for Step 2*)
f3[col_,t_]:=Flatten[{col,Table[j,{j,r-(t-Length[col]-2),r}],Table[-j,{j,r,t,-1}]}];
(*filling function for step 3*)
f4[t_]:=Flatten[{Table[j,{j,1,(r+t-1)/2}],Table[-j,{j,(r+t-1)/2,t,-1}]}];
(*for tableaux containing only even steps*)
If[Apply[And,Map[EvenQ[#[[2]] ]&,num] ],
Return[Join[vacleft,Flatten[Table[{f1[rectab[[i]] ],f2[rectab[[i]] ]},
{i,1,s-Length[vacleft],2}],1]](*Return*)](*If*)];
(*cri gives the height of the first odd step*)
cri=num[[Min[Position[Map[OddQ[#[[2]] ]&,num],True]]  ]][[1]];
(*filling by Step 1 without vacuum columns on the left*)
middle=Most[Select[rectab,Length[#]>=cri&]];
middle=Flatten[Table[{f1[rectab[[i]] ],f2[rectab[[i]] ]},
{i,1,Length[middle]-1,2}],1];
(*filling by Step 2*)
side=Drop[rectab,Length[middle]+1];
t=cri+1;
For[i=1,i<=Length[side],i++,
side=ReplacePart[side,i->f3[side[[i]],t]];
t=side[[i,Length[rectab[[Length[middle]+1+i]] ]+1 ]]
(*For*)];
Join[vacleft,middle,side,{f4[t]}]
]




(* Draw RC [Aug/2011]
Example 1
showRC[{{{4}, {2, 3}, {1, 3}, {4, 3}, {2}}, {{2}, {3, 2, 1}, {2, 2, 1,
     1}, {2, 2, 1, 1, 1, 1}, {3, 2, 1, 1, 1, 1}, {2, 1, 1}, {2, 
    2}}, {{2}, {1, 0, 0}, {4, 1, 2, 1}, {1, 0, 0, 0, 0, 0}, {0, 1, 0, 
    0, 0, 0}, {0, 0, 0}, {0, 0}}}]
Example 2
showRC[{{{4, 4, 3, 3, 2, 2, 2, 2, 1, 1}}, {{9, 3, 2, 2, 2, 1, 1}, {9, 
    3, 2, 1, 1}, {4, 1, 1}, {}, {}, {}}, {{-1, 2, 2, 1, 0, 1, 
    0}, {-6, -2, -1, 0, 0}, {-1, -1, -1}, {}, {}, {}}}]
*)
tocell[yng_] := 
 Flatten[Table[
   Table[{i, Length[yng] - j}, {i, 1, yng[[j]]}], {j, 1, 
    Length[yng]}], 1]

vaclis[rc_, a_] := 
 Table[vac[rc, a, rc[[2, a, i]] ], {i, 1, Length[rc[[2, a]] ]}]

vacexp[rc_, a_] := Module[{str},
  str = vaclis[rc, a];
  Table[Text[
    Style[str[[i]], FontSize -> 12, FontFamily -> "Helvetica"], {0.6, 
     Length[str] - i + 0.4}, Right], {i, 1, Length[str]}]]

rigexp[rc_, a_] :=
 Module[{l = Length[rc[[2, a]] ]}, 
  Table[Text[
    Style[rc[[3, a, i]], FontSize -> 12, 
     FontFamily -> "Helvetica"], {rc[[2, a, i]] + 1.4, l - i + 0.4}, 
    Left], {i, 1, l}]]

showRCpart[rc_, a_] := 
 Graphics[Join[{FaceForm[], EdgeForm[Directive[Thin]]}, 
   Map[Rectangle[#] &, tocell[rc[[2, a]] ]], vacexp[rc, a], 
   rigexp[rc, a]], 
  ImageSize -> 
    Max[rc[[2, a]] ]*12
+If[ vaclis[rc, a][[1]] < 0, 20,10]
+If[Min[Take[rc[[3,a]],Count[rc[[2,a]], Max[rc[[2,a]] ] ] ] ]<0, 20,10]
]

showRC[rc_] := 
 If[rc == {}, {}, 
  Grid[{Table[
     If[Length[rc[[2, a]] ] == 0, Text[\[EmptySet]], 
      showRCpart[rc, a]], {a, 1, Length[rc[[2]] ]}]}, 
   Alignment -> {Automatic, Top}]]



(* Crystal Operators on RC [Aug/2011] & [Sep/2013]
frc[{{{4, 4, 3, 3, 2, 2, 2, 2, 1, 1}}, {{6, 4, 3, 1, 1}, {5, 4, 
    2}, {6, 1}, {}, {}, {}}, {{3, 1, 0, 0, 
    0}, {-2, -3, -1}, {-3, -1}, {}, {}, {}}}, 2] *)

(* fpos gives position of the cell to be added by f_a;
answer given as the position in the list *)
fpos[rc_, a_] := Module[{rig},
  If[Min[rc[[3, a]] ] > 0, Return[Length[rc[[2, a]] ] + 1]];
  rig = Position[rc[[3, a]], Min[rc[[3, a]] ]];
  Min[Intersection[
    Position[rc[[2, a]], Max[Extract[rc[[2, a]], rig]]], rig]] ]

frc[rc_, a_] := Module[{pos, thre, ans},
  pos = fpos[rc, a];
  thre = Append[rc[[2, a]], 0][[pos]];
  ans = ReplacePart[rc,
    {{2, a} -> 
      If[thre == 0, Append[rc[[2, a]], 1], 
       MapAt[# + 1 &, rc[[2, a]], pos] ],
     {3, a - 1} -> 
      If[a == 1 ||a==Length[rc[[2]] ]|| rc[[3, a - 1]] == {}, rc[[3, a - 1]], 
       Table[If[rc[[2, a - 1, i]] > thre, rc[[3, a - 1, i]] + 1, 
         rc[[3, a - 1, i]] ], {i, 1, Length[rc[[2, a - 1]] ]}] ],
     {3, a + 1} -> 
      Which[a==Length[rc[[2]] ]-1,rc[[3,a+1]],
a < Length[rc[[2]]  ] && rc[[3, a + 1]] != {}, 
       Table[If[rc[[2, a + 1, i]] > thre, rc[[3, a + 1, i]] + 1, 
         rc[[3, a + 1, i]] ], {i, 1, Length[rc[[2, a + 1]] ]}],
       a < Length[rc[[2]]  ] && rc[[3, a + 1]] == {}, {}],
     {3, a} -> 
      Table[If[rc[[2, a, i]] > thre, rc[[3, a, i]] - 2, 
        rc[[3, a, i]] ], {i, 1, Length[rc[[2, a]] ]}]
     }];
(*a=n*)
ans=If[a==Length[rc[[2]] ],
ReplacePart[ans,{3,a-2}->
Table[If[ans[[2, a - 2, i]] > thre, ans[[3, a - 2, i]] + 1, 
         ans[[3, a - 2, i]] ], {i, 1, Length[ans[[2, a - 2]] ]}]   ],
ans];
(*a=n-2*)
ans=If[a==Length[rc[[2]] ]-2,
ReplacePart[ans,{3,a+2}->
Table[If[ans[[2, a + 2, i]] > thre, ans[[3, a + 2, i]] + 1, 
         ans[[3, a + 2, i]] ], {i, 1, Length[ans[[2, a + 2]] ]}] ],
ans];
  ans = If[thre == 0, MapAt[Append[#, -1] &, ans, {3, a}],
    ReplacePart[ans, {3, a, pos} -> rc[[3, a, pos]] - 1 ]];
  If[vac[ans, a, thre + 1] < ans[[3, a, pos]], 0, ans ]]

erigchange[rc_, a_, el_, same_] := Switch[same,
  1, MapAt[# + 2 &, rc, 
   Table[{3, a, i}, {i, 1, Length[Select[rc[[2, a]], # >= el &]]}] ],
  0, MapAt[# - 1 &, rc, 
   Table[{3, a, i}, {i, 1, Length[Select[rc[[2, a]], # >= el &]]}] ]
  ]

erc[rc_, a_] := Module[{xl = Min[rc[[3, a]] ], el, epos, ans},
  If[xl >= 0, Return[0]];
  ans = rcnorder[rc];
  epos = Max[Position[ans[[3, a]], xl]];
  el = ans[[2, a, epos]];
  ans = MapAt[# - 1 &, ans, {2, a, epos}];
  ans = MapAt[# + 1 &, ans, {3, a, epos}];
  ans = If[el == 1, Delete[ans, {{2, a, epos}, {3, a, epos}}], ans];
  ans = Which[a == 1, erigchange[erigchange[ans, 1, el, 1], 2, el, 0],
    a == Length[rc[[2]] ], 
    erigchange[erigchange[ans, a, el, 1], a - 2, el, 0],
    a == Length[rc[[2]] ] - 1, 
    erigchange[erigchange[ans, a, el, 1], a - 1, el, 0],
    a == Length[rc[[2]] ] - 2, 
    erigchange[
     erigchange[erigchange[erigchange[ans, a, el, 1], a + 2, el, 0], 
      a + 1, el, 0], a - 1, el, 0],
    True, 
    erigchange[erigchange[erigchange[ans, a, el, 1], a - 1, el, 0], 
     a + 1, el, 0]
    ];
  ans
  ]
