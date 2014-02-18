(* Mathematica Package *)

BeginPackage["Genfunlib`GFeqn2coefs`"]

CoefsByDerivs::usage = "CoefsByDerivs[{eqn1, eqn2,...}, {f,g, ...}, " <>
    "{x, 0, nx}, {y, 0, ny}, ...] gives the Taylor expansions at (0,0,...) " <>
    "of the power series f,g,... satisfying the equations.";
CoefsByNewton::usage = "CoefsByNewton[eqn, f, {x, 0, nx}] gives the " <>
    "Maclaurin expansion in x of f satisfying eqn.";

Begin["`Private`"] (* Begin Private Context *) 

(* what can usually be used as a variable, according to 
    ref/message/General/ivar *)
variablePattern = Except[_String | _?NumberQ | _Plus | _Times | 
    _Sum | _Product | _^_Integer];

CoefsByDerivs::invalid = "Invalid input.";
CoefsByNewton::invalid = "Invalid input.";
CoefsByDerivs::invalidArgumentSyntax = "Invalid argument syntax.";
CoefsByNewton::invalidArgumentSyntax = "Invalid argument syntax.";

(* validate the equation or system of equations that the user supplies *)

validateSystem[system : {HoldPattern[_ == _]..}, series: { variablePattern.. }, 
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
    ok = ok && (D[lhs - rhs, series] /. {var->0, series->0}) =!= 0;

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

CoefsByDerivs[___] /; (Message[CoefsByDerivs::invalidArgumentSyntax]; False) := 
    Null;

CoefsByNewton[lhs_ == rhs_, series_, {var_, 0, n_}] := Module[
   {
    f = lhs - rhs, ff, m = 2^Ceiling[Log[2, n]],
    approx = First[
     (series/.var->0) /. Solve[(lhs==rhs)/.var->0, series/.var->0]]
   },
   (
   ff[z_] := (f /. series :> z);
   Do[
    approx = Normal[# - ff[#]/ff'[#] &[approx] + O[var]^(2^k)], 
    {k, 1, Log[2, m] + 1}
   ];
   approx + O[var]^(n + 1)
   )/; validateEquation[lhs==rhs, series, {var, 0, n}] 
   ];

CoefsByNewton[___] /; (Message[CoefsByNewton::invalidArgumentSyntax]; False) := 
    Null;

End[] (* End Private Context *)

EndPackage[]
