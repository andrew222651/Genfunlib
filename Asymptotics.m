(* Mathematica Package *)

BeginPackage["Genfunlib`Asymptotics`"]

(*Begin["`Private`"]*)(*jft*)
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

reduction[y : 1/(1 + arg_), x_] := Module[
   {
    arga, argp
    },
   {arga, argp} = reduction[-arg, x];
   {0, GCD[arga, argp]}
   ];

reduction[y : Log[1/(1 + arg_)], x_] := Module[
   {
    arga, argp
    },
   {arga, argp} = reduction[-arg, x];
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

reduction[Power[expr_, j_Integer?Positive], x_] := radius[Unevaluated[
    expr * Power[expr, j - 1]], x];
reduction[Power[expr_, j_Integer?(#<-1&)], x_] := radius[Unevaluated[
    Power[expr, -1] * Power[expr, j + 1]], x];
 
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
       SeriesData[n, DirectedInfinity[1], {(p*d1)/(2*Sqrt[Pi]), 0},
         3, 5, 2],
      r^-n*
       SeriesData[n, DirectedInfinity[1], {d1/(2*Sqrt[Pi]), 0}, 3, 
        5, 2]
      ]
     ) /; (! (PolynomialQ[expr, y[z]] && Exponent[expr, y[z]] == 1)) &&
      SeriesCoefficient[expr, {y[z], 0, 0}] != 0
   ];

radius[y_, x_] /; PolynomialQ[y, x] := Infinity;

radius[Exp[y_], x_] := radius[y, x];

radius[1/(1 + y_), x_] := Module[
   {
    res, r, nres
    },
   res = Solve[-y == 1 && x > 0, x];
   r = If[MatchQ[res, {__List}],
     Min[x /. res],
     nres = NSolve[-y == 1 && x > 0, x];
     Min[x /. nres]
     ];
   r
   ];

radius[Log[1/(1 + y_)], x_] := Module[
   {
    res, r, nres
    },
   res = Solve[-y == 1 && x > 0, x];
   r = If[MatchQ[res, {__List}],
     Min[x /. res],
     nres = NSolve[-y == 1 && x > 0, x];
     Min[x /. nres]
     ];
   r
   ];

radius[term1_ + term2_, x_] := Min[radius[term1, x], radius[term2, x]];

radius[factor1_*factor2_, x_] := Min[radius[factor1, x], radius[factor2, x]];

radius[Power[expr_, j_Integer?Positive], x_] := radius[Unevaluated[
    expr * Power[expr, j - 1]], x];
radius[Power[expr_, j_Integer?(#<-1&)], x_] := radius[Unevaluated[
    Power[expr, -1] * Power[expr, j + 1]], x];
 

directions[Exp[expr_], x_] := directions[expr, x];

directions[1/(1 + expr_), x_] := Module[
   {
    a, p, q
    },
   {a, p} = reduction[-expr, x];
   q = GCD[a, p];
   2*Range[1, q]*Pi/q
   ];

directions[Log[1/(1 + expr_)], x_] := Module[
   {
    a, p, q
    },
   {a, p} = reduction[-expr, x];
   q = GCD[a, p];
   2*Range[1, q]*Pi/q
   ];

directions[(Plus | Times)[term1_, term2_], x_] := Module[
   {
    r1 = radius[term1, x],
    r2 = radius[term2, x]
    },
   If[r1 < r2,
    Return[directions[term1, x]]
    ];
   If[r1 > r2,
    Return[directions[term2, x]]
    ];
   Return[Union[directions[term1, x], directions[term2, x]]];
   ];

directions[Power[expr_, j_Integer?Positive], x_] := directions[Unevaluated[
    expr * Power[expr, j - 1]], x];
directions[Power[expr_, j_Integer?(#<-1&)], x_] := directions[Unevaluated[
    Power[expr, -1] * Power[expr, j + 1]], x];

allimit[1/(1 + expr_), x_] := Module[
   {
    r = radius[1/(1 + expr), x]
    },
   {1/(r*D[-expr, x] /. x -> r), -1, 0, r}
   ];

allimit[Log[1/(1 + expr_)], x_] := Module[
   {
    r = radius[Log[1/(1 + expr)], x]
    },
   {1, 0, 1, r}
   ];

allimit[Exp[expr_], x_] := Module[
   {
    expra, exprb, exprc, exprr,
    r = radius[Exp[expr], x]
    },
   {exprc, expra, exprb, exprr} = allimit[expr, x];
   If[MatchQ[{exprc, expra, exprb, exprr}, {_, 0, 1, r}],
    {Exp[exprb], -expra, 0, r},
    experr
    ]
   ];

allimit[term1_ + term2_, x_] := Module[
   {
    term1limit, term1a, term1b, term1c, term1r,
    term2limit, term2a, term2b, term2c, term2r
    },
   term1limit = {term1c, term1a, term1b, term1r} = allimit[term1, x];
   term2limit = {term2c, term2a, term2b, term2r} = allimit[term2, x];
   If[term1r < term2r,
    Return[term1limit];
    ];
   If[term2r > term1r,
    Return[term1limit];
    ];
   If[term1a < term2a,
    Return[term1limit];
    ];
   If[term2a < term1a,
    Return[term2limit];
    ];
   If[term1b > term2b,
    Return[term1limit];
    ];
   If[term2b > term1b,
    Return[term2limit];
    ];
   {term1c + term2c, term1a, term1b, term1r}
   ];

allimit[factor1_*factor2_, x_] := Module[
   {
    factor1limit, factor1a, factor1b, factor1c, factor1r,
    factor2limit, factor2a, factor2b, factor2c, factor2r
    },
   factor1limit = {factor1c, factor1a, factor1b, factor1r} = 
     allimit[factor1, x];
   factor2limit = {factor2c, factor2a, factor2b, factor2r} = 
     allimit[factor2, x];
   If[factor1r < factor2r,
    Return[{factor1c*(factor2 /. x -> factor1r), factor1a, factor1b, 
       factor1r}];
    ];
   If[factor2r < factor1r,
    Return[{(factor1 /. x -> factor2r)*factor2c, factor2a, factor2b, 
       factor2r}];
    ];
   {factor1c*factor2c, factor1a + factor2a, factor1b + factor2b, factor1r}
   ];

allimit[Power[expr_, j_Integer?Positive], x_] := allimit[Unevaluated[
    expr * Power[expr, j - 1]], x];
allimit[Power[expr_, j_Integer?(#<-1&)], x_] := allimit[Unevaluated[
    Power[expr, -1] * Power[expr, j + 1]], x];

allimit[poly_, x_] /; PolynomialQ[poly,x] := {poly /. x-> Infinity, 
   0, 0, Infinity};

alcoeflimit[expr_, x_, n_] := Module[
   {
    r = radius[expr, x],
    dirs = directions[expr, x],
    expra, exprb, exprc, exprr
    },
   If[dirs != {2 * Pi} || r == Infinity,
    Return[err];
    ];
   {exprc, expra, exprb, exprr} = allimit[expr, x];
   If[expra > 0,
    exprc*exprr^-n (n^-expra Log[n]^exprb)/(n*Gamma[-expra]),
    huh
   ];

(*End[]*)
EndPackage[]
