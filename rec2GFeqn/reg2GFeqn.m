(* Mathematica Package *)

BeginPackage["rec2GFeqn`"]
(* Exported symbols added here with SymbolName::usage *)  

Begin["`Private`"] (* Begin Private Context *) 
(* problem solved: just take GeneratingFunction of both sides. \
GeneratingFunction could be extended to operations corresponding to \
integration. *)

Clear[toGFeqn, gf, bounds, ratFactor]

(* takes recurrence relation for Subscript[(a[n]), n>=0] which holds \
for n>=0 *)
toGFeqn[lhs_ == rhs_] := 
  gf[sum[lhs*z^n, {n, 0, Infinity}]] == 
   gf[sum[rhs*z^n, {n, 0, Infinity}]];

(* break things up *)
gf[sum[expr_, {s__}]] := gf[sum[Expand@Apart@expr, {s}]];

(* sum *)
gf[sum[a_ + b_, {s__}]] := gf[sum[a, {s}]] + gf[sum[b, {s}]];

(* free *)
gf[sum[expr_?(FreeQ[#, a] &), {s__}]] := Sum[expr, {s}];

(* scalar multiplication *)
gf[sum[c_?(FreeQ[#, a] && FreeQ[#, n] &)*expr_, {s__}]] := 
  c*gf[sum[expr, {s}]];

(* sumless *)
gf[sum[(fac_: 1)*a[n + j_: 0]*z^n, {n, l_, u_}]] := 
  z^-j*bounds[sum[(fac /. n -> n - j)*a[n] z^n, {n, l + j, u + j}]];

bounds[sum[expr_, {n, l_, u_}]] := 
  ratFactor[sum[expr, {n, 0, u}]] - Sum[expr, {n, 0, l - 1}];

ratFactor[sum[n^(k_: 1)*fac_*a[n]*z^n, {n, 0, u_}]] /; k >= 1 := 
  x*D[ratFactor[sum[n^(k - 1)*fac*a[n]*z^n, {n, 0, u}]], z];

ratFactor[sum[(n + j_)^k_*fac_*a[n]*z^n, {s__}]] /; k <= -1 := 
  z^-j Integrate[
    ratFactor[
     sum[(n + j)^(k + 1)*fac*a[n]*t^(n + k - 1), {n, 0, u_}]], {t, 0, 
     z}];

ratFactor[sum[a[n]*z^n, {s__}]] := aa[z];

(* TODO: GF multiplication and composition *)
End[] (* End Private Context *)

EndPackage[]