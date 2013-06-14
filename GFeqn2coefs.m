(* Mathematica Package *)

BeginPackage["Genfunlib`GFeqn2coefs`"]

CoefsByDerivs::usage = "CoefsByDerivs[{eqn1, eqn2,...}, {f,g, ...}, " <>
    "{x, 0, nx}, {y, 0, ny}, ...] gives the Maclaurin expansions of the " <>
    "power series f,g,... satisfying the equations.";
CoefsByNewton::usage = "CoefsByNewton[eqn, f, {x, 0, nx}] gives the " <>
    "Maclaurin expansion in x of f satisfying eqn.";

Begin["`Private`"] (* Begin Private Context *) 

(* what can usually be used as a variable, according to 
    ref/message/General/ivar *)
variablePattern = Except[_String | _?NumberQ | _Plus | _Times | 
    _Sum | _Product | _^_Integer];

CoefsByDerivs::invalid = "Invalid input.";
CoefsByNewton::invalid = "Invalid input.";

validateSystem[system : {(x_ == _)..}, series: { variablePattern[__].. }, 
    iters:({variablePattern, 0, _Integer?NonNegative}..)] := Module[
    {
        ok = True
    },
    If[ !ok, Message[CoefsByDerivs::invalid]];
    ok
];

validateSystem[___] := (Message[CoefsByDerivs::invalid];False);

validateEquation[lhs_ == rhs_, series:variablePattern, 
    {var:variablePattern, 0, _Integer?NonNegative}] := Module[
    {ok = True},

    ok = ok && !FreeQ[series, var] && !FreeQ[lhs-rhs, series];
    ok = ok && D[lhs - rhs, series] =!= 0;

    If[ !ok, Message[CoefsByNewton::invalid]];
    ok
];

validateEquation[___] := (Message[CoefsByNewton::invalid];False);

CoefsByDerivs[x:Except[_List], y__] := CoefsByDerivs[{x}, y];
CoefsByDerivs[x_, y:Except[_List], z__] := CoefsByDerivs[x, {y}, z];

CoefsByDerivs[system_, series_, iters__] := Module[
   {
    indets = {iters} /. {x_, 0, _} :> x,
    systemCanon = system /. (l_ == r_ :> l - r),
    expansion,
    eqns, subs
    },
   (
     expansion = Normal[Series[systemCanon, iters]];
     eqns = Thread[Flatten[CoefficientList[expansion, indets]] == 0];
     subs = Flatten[Solve[eqns]];
     Thread[series == (Series[series, iters] /. subs)]
     ) /; validateSystem[system, series, iters]
   ];

CoefsByNewton[lhs_ == rhs_, series_, {var_, 0, n_}] := Module[
   {
    f = lhs - rhs, ff, approx = 0, m = 2^Ceiling[Log[2, n]]
   },
   (
   ff[z_] := Normal[(f /. series :> z) + O[var]^m];
   Do[
    approx = Normal[# - ff[#]/ff'[#] &[approx] + O[var]^(2^k)], 
    {k, 1, Log[2, m]}
   ];
   approx + O[var]^(n + 1)
   )/; validateEquation[lhs==rhs, series, {var, 0, n}] 
   ];

End[] (* End Private Context *)

EndPackage[]
