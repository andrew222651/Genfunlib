(* Mathematica Package *)

BeginPackage["Genfunlib`GFeqn2coefs`"]

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

End[] (* End Private Context *)

EndPackage[]