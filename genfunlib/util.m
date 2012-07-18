(* Mathematica Package *)

BeginPackage["genfunlib`util`"]

egf2ogf::usage = "efg2ogf[f, z] gives the OGF form of the EGF f in the indeterminate z";
ogf2egf::usage = "ofg2egf[f, z] gives the EGF form of the OGF f in the indeterminate z";

Begin["`Private`"] 

egf2ogf[egf_, indet_] := Module[
   {temp},
   (LaplaceTransform[egf, indet, 1/temp]/temp // Simplify) /. 
    temp -> indet
   ];

(* egf2ogf = ogf2egf^-1 *)
ogf2egf[ogf_, indet_] := Module[
   {temp1, temp2}, 
   InverseLaplaceTransform[(ogf /. {indet -> 1/temp1})/temp1, temp1, 
     temp2] /. temp2 -> indet
   ];
   
End[] 

EndPackage[]