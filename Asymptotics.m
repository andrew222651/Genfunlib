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

(* assumes expr is from elementary iterative class, so characteristic \
eqn is satisfied and period is computed *)
saiv[y_[z_] == z_*expr_, n_] := Module[
   {
    period = reduction[expr, y[z]], p,
    t, res, nres,
    d1, r
    },
   (
     p = If[period[[2]] == Infinity,
       period[[1]], period[[2]]];
     res = Solve[expr - y[z]*D[expr, y[z]] == 0 && y[z] > 0, y[z]];
     If[MatchQ[res, {__List}],
      t = Min[y[z] /. res],
      nres = 
       NSolve[expr - y[z]*D[expr, y[z]] == 0 && y[z] > 0, y[z]];
      t = Min[y[z] /. nres]
      ];
     r = t/(expr /. y[z] -> t);
     d1 = Sqrt[(2*(expr /. y[z] -> t))/(
      D[expr, {y[z], 2}] /. y[z] -> t)];
     If[p >= 2,
      Boole[Mod[n, p] == 1]*r^-n*
       SeriesData[n, DirectedInfinity[1], {(p*d1)/(2*Sqrt[\[Pi]]), 0},
         3, 5, 2],
      r^-n*
       SeriesData[n, DirectedInfinity[1], {d1/(2*Sqrt[\[Pi]]), 0}, 3, 
        5, 2]
      ]
     ) /; (! (PolynomialQ[expr, y[z]] && Exponent[expr, y[z]] == 1)) &&
      SeriesCoefficient[expr, {y[z], 0, 0}] != 0
   ];
EndPackage[]
