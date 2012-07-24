(* Mathematica Package *)

BeginPackage["genfunlib`GFeqn2coefs`"]

Begin["`Private`"] (* Begin Private Context *) 

coefs[eqn_, n_, func_, indet_] := 
     Module[{system = Table[
             D[eqn, {indet, k}] /. indet -> 0, 
             {k, 0, n}], 
             derivs = 
           Table[Derivative[k][func][0], 
             {k, 0, n}], solutions}, 
       solutions = Solve[system, derivs]; 
        First[derivs /. solutions]]; 

End[] (* End Private Context *)

EndPackage[]