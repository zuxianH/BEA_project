(* ::Package:: *)

(* ::Input:: *)
(*Quiet[Needs["Combinatorica`"]];*)


(* ::Input:: *)
(*Endpoints[\[Lambda]_]:=Join[{{0,\[Lambda][[1]]}},Flatten[Table[{a,s},{a,1,Length[\[Lambda]]-1},{s,\[Lambda][[a+1]],\[Lambda][[a]]}],1],Table[{Length[\[Lambda]],s},{s,0,\[Lambda][[Length[\[Lambda]]]]}]]*)
(**)
(*PathsAtoB[A_, B_] := Block[{paths},*)
(*  	paths = {};*)
(*  	findPaths[{x_, y_}, {xMax_, yMax_}, currentPath_] := Module[{},*)
(*    	If[{x, y} == {xMax, yMax}, AppendTo[paths, currentPath];*)
(*     	Return[];];*)
(*    	If[x + 1 <= xMax, *)
(*     findPaths[{x + 1, y}, {xMax, yMax}, *)
(*      Append[currentPath, {x + 1, y}]]];*)
(*    	If[y + 1 <= yMax, *)
(*     findPaths[{x, y + 1}, {xMax, yMax}, *)
(*      Append[currentPath, {x, y + 1}]]];]*)
(*  ; findPaths[A, B, {A}]; *)
(*  paths] (*All paths between points A and B (both coordinates {x,y})*)*)
(**)
(*AllPaths[shape_] :=Block[{}, Flatten[PathsAtoB[{0,0}, #] & /@ Endpoints[shape], 1]] (*All possible paths from the corner of the Young diagram *)*)
(**)
(*KDpath[shape_] :=Select[AllPaths[shape],Total[#, {1, 2}] == Min[Total[AllPaths[shape], {2, 3}]] &] (*Kac-Dynkin path that minimises number of Bethe roots; in case there are several, we store all*)*)


(* ::Input:: *)
(*markedPoint[yd_]:=KDpath[yd][[1,-1]]*)


(* ::Input:: *)
(*lambdaMarked[yd_,markedPoint_]:=Table[yd[[a]]-a-markedPoint[[2]]+markedPoint[[1]],{a,markedPoint[[1]]}];*)
(*nuMarked[yd_,markedPoint_]:=Table[TransposePartition[yd][[i]]-i-markedPoint[[1]]+markedPoint[[2]],{i,markedPoint[[2]]}];*)
(**)
(*mP=markedPoint[yd];*)
(**)
(*\[Lambda]marked=lambdaMarked[yd,mP];*)
(*\[Nu]marked=nuMarked[yd,mP];*)
(*mMarked[A_,J_]:=Sum[\[Lambda]marked[[a]],{a,A}]+Sum[\[Nu]marked[[i]],{i,J}]-Length[A](Length[A]-1)/2-Length[J](Length[J]-1)/2+Length[A]Length[J];*)


(* ::Input:: *)
(*Q[A_List,J_List]:=u^mMarked[A,J]+Sum[c[A,J][k]u^(mMarked[A,J]-k),{k,1,mMarked[A,J]}]/.c[A,J][i_]:>Which[Length[A]==1&&Length[J]==0&&MemberQ[\[Lambda]marked,mMarked[A,J]-i],0,Length[A]==0&&Length[J]==1&&MemberQ[\[Nu]marked,mMarked[A,J]-i],0,True,c[A,J][i]]*)


(* ::Input:: *)
(*Do[coeffs[{a},{i}]=Solve[(cfs=CoefficientList[((Q[{a},{i}]/.(u->u+I/2))-(Q[{a},{i}]/.(u->u-I/2))),u])/cfs[[-1]]-CoefficientList[Q[{a},{}]Q[{},{i}],u]==0,CoefficientList[Q[{a},{i}],u][[2;;-2]]][[1]],{a,1,mP[[1]]},{i,1,mP[[2]]}]*)


(* ::Input:: *)
(*fermlist=Table[(Q[{i},{j}]/.coeffs[{i},{j}])/. u -> (u + hbar*((mP[[1]]-mP[[2]])/2 )),{i,mP[[1]]},{j,mP[[2]]}];*)


(* ::Input:: *)
(*boslist=Table[(Q[{i},{}])/. u -> (u + hbar*((mP[[1]]-mP[[2]]-2j+1)/2 )),{i,mP[[1]]},{j,mP[[1]]-mP[[2]]}]/.hbar->I;*)


(* ::Text:: *)
(*The equation 2.20 in Chernyak & Volin*)


(* ::Input:: *)
(*SusyWronskian=(-1)^(mP[[2]](mP[[1]]-mP[[2]]))Det[ArrayFlatten[{{fermlist,boslist}}]] (*The RHS of 2.20 in Chernyak&Volin*)*)


(* ::Input:: *)
(*YQ\[Theta][0,0,YD_]:=Product[u-\[Theta][i],{i,Total[YD]}] (*The LHS of 2.20*)*)
