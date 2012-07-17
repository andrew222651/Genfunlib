(* Mathematica Package *)

BeginPackage["util`"]
(* Exported symbols added here with SymbolName::usage *)  

Begin["`Private`"] (* Begin Private Context *) 
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
End[] (* End Private Context *)

EndPackage[]