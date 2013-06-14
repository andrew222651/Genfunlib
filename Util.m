(* Mathematica Package *)

BeginPackage["Genfunlib`Util`"]

Egf2ogf::usage = "Efg2ogf[f, z] gives the OGF form of the EGF f in the " <>
"indeterminate z";
Ogf2egf::usage = "Ofg2egf[f, z] gives the EGF form of the OGF f in the " <>
" indeterminate z";

Begin["`Private`"] 

Egf2ogf[egf_, indet_] := Module[
   {temp},
   (LaplaceTransform[egf, indet, 1/temp]/temp // Simplify) /. 
    temp -> indet
   ];

(* egf2ogf = ogf2egf^-1 *)
Ogf2egf[ogf_, indet_] := Module[
   {temp1, temp2}, 
   InverseLaplaceTransform[(ogf /. {indet -> 1/temp1})/temp1, temp1, 
     temp2] /. temp2 -> indet
   ];
   
End[] 

EndPackage[]
