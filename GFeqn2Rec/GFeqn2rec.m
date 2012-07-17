(* Mathematica Package *)

BeginPackage["GFeqn2rec`"]
(* Exported symbols added here with SymbolName::usage *)  

Begin["`Private`"] (* Begin Private Context *) 
(* extract coefficients from both sides of an equation (as-is) in \
a[x] and x *)

Clear[co]

(* addition *)
co[a_ + b_, n_] := co[a, n] + co[b, n];

(* [(x^n)]a[x] *)
co[a[x], n_] := cof[n];

(* expressions free of "a" *)
co[expr_?(FreeQ[#, a] &), n_] := SeriesCoefficient[expr, {x, 0, n}];

(* scaling (can produce simpler expressions than multiplication) *)
co[fac_?(FreeQ[#, a] &)*expr_?(! FreeQ[#, a] &), n_] := 
  fac*co[expr, n];

(* shift (can produce simpler expressions than multiplication) *)
co[x^(k_: 1)*expr_, n_] := Boole[n - k >= 0] co[expr, n - k];

(* multiplication *)
co[expr1_*expr2_, n_] := With[
   {iterator = Unique[]}, 
   Sum[co[expr1, iterator] co[expr2, n - iterator], {iterator, 0, n}]
   ];

(* derivatives *)
co[Derivative[k_][a][x], n_] := Pochhammer[n + 1, k] cof[n + k]

co[FullForm[Integrate[a[t_Symbol], 
           {t_, 0, x}]], n_] := 
     Boole[n >= 1]*(1/n)*cof[n - 1]; 

(* thread over equations *)
co[expr1_ == expr2_, n_] := co[expr1, n] == co[expr2, n];

(* powers of a[x] *)

co[a[x]^(k_), n_] := 
     co[Unevaluated[a[x]*
           a[x]^(k - 1)], n]; 

(* TODO: compositions -- f[a[x]] and a[f[x]].
   general composition is too unhelpful, if there are specific cases \
like a[k_*x] that are simple, they could be implemented. *)
End[] (* End Private Context *)

EndPackage[]