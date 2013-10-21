(* Mathematica Package *)

BeginPackage["Genfunlib`Asymptotics`"]

Begin["`Private`"]
protected = Unprotect[GCD, Mod];

GCD[Infinity, rest__] := GCD[rest];

GCD[0] := Infinity;

Mod[n_, Infinity] := n;

Protect[Evaluate[protected]];

exponents[y_, x_] := 
  Union[Flatten[CoefficientRules[y, x][[All, 1]]]];

reduction[y_, x_] := Module[
   {exps = exponents[y, x]},
   (
     If[Length[exps] == 1,
      {First[exps], Infinity},
      {Mod[First[exps], GCD @@ Differences[exps]], 
       GCD @@ Differences[exps]}
      ]
     ) /; PolynomialQ[y, x]
   ];

reduction[y : 1/(1 - arg_), x_] := Module[
   {
    arga, argp
    },
   {arga, argp} = reduction[arg, x];
   {0, GCD[arga, argp]}
   ];

reduction[y : Log[1/(1 - arg_)], x_] := Module[
   {
    arga, argp
    },
   {arga, argp} = reduction[arg, x];
   {0, GCD[arga, argp]}
   ];

reduction[y : Exp[arg_], x_] := Module[
   {
    arga, argp
    },
   {arga, argp} = reduction[arg, x];
   {0, GCD[arga, argp]}
   ];

(* proof: give equiv def of a and p in terms of GCD and mod,
show that the following supplies that; note: term1a=term2a (mod pp) *)

reduction[term1_ + term2_, x_] := Module[
   {
    term1a, term1p, term2a, term2p,
    pp
    },
   {term1a, term1p} = reduction[term1, x];
   {term2a, term2p} = reduction[term2, x];
   pp = GCD[term1p, term2p, term1a - term2a];
   {Mod[term1a, pp], pp}
   ];

reduction[term1_*term2_, x_] := Module[
   {
    term1a, term1p, term2a, term2p,
    pp
    },
   {term1a, term1p} = reduction[term1, x];
   {term2a, term2p} = reduction[term2, x];
   pp = GCD[term1p, term2p];
   {Mod[term1a + term2a, pp], pp}
   ];
End[]

EndPackage[]
