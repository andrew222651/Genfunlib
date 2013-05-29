(* Mathematica Package *)

BeginPackage["Genfunlib`GFeqn2coefs`"]

CoefsByDerivs::usage = "";
CoefsByNewton::usage = "";

Begin["`Private`"] (* Begin Private Context *) 

coefs[eqn_, n_, func_, indet_] := 
     Module[
 {
  renamedFunc,
  renamedEqn , k
  },
 renamedEqn = eqn /. func -> renamedFunc;
 Do[
  Derivative[k][renamedFunc][0] = 
   First@(Derivative[k][renamedFunc][0] /. 
      Solve[renamedEqn /. indet -> 0, Derivative[k][renamedFunc][0]]);
  renamedEqn = D[renamedEqn, indet],
  {k, 0, n}];
 (Derivative[#][renamedFunc][0]/#! &) /@ Range[0, n]
 ]; 

(* http://www.mathematik.uni-kassel.de/~koepf/Publikationen/Koepf-\
Newton2008.pdf *)

fastImplicitTaylor[
   lhs_ == rhs_, x_[t_], x0_, n_
   ] := Module[{
    f = lhs - rhs, ff, approx, z, k, 
    m = -1 + 2^\[LeftCeiling]Log[2, n]\[RightCeiling]
    },
   ff[z_] := Normal[(f /. x[t] :> z) + O[t]^(m + 1)];
   approx = x0;
   Do[
    approx = Normal[# - ff[#]/ff'[#] &[approx] + O[t]^(2^k)], {k, 1, 
     Log[2, m + 1]}];
   approx + O[t]^(n + 1)
   ];

End[] (* End Private Context *)

EndPackage[]
