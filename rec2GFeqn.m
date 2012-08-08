(* Mathematica Package *)

BeginPackage["Genfunlib`rec2GFeqn`"]

Begin["`Private`"] (* Begin Private Context *) 

(* break things up *)
gf[sum[expr_, {s__}]] := gf[sum[Expand@Apart@expr, {s}]];

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