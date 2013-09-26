(* Mathematica Package *)

BeginPackage["Genfunlib`rec2GFeqn`"]

Begin["`Private`"] 

(* http://mathematica.stackexchange.com/questions/32531/how-to-unprotect-generatingfunction/32533#32533 *)
GeneratingFunction;
protected = Unprotect[GeneratingFunction];

(* what can usually be used as a variable, according to 
	ref/message/General/ivar *)
variablePattern = Except[_String | _?NumberQ | _Plus | _Times | 
	_Sum | _Product | _^_Integer];

arg2 = Sequence[n:variablePattern, x:variablePattern];

(* rational function (over syntactic integers) coefficients *)
(* http://mathematica.stackexchange.com/a/32611/208 *)
    (* partial fraction expansion *)
GeneratingFunction[expr_, arg2, 
    opts:OptionsPattern[]] /; expr =!= Apart[expr, n] :=
    GeneratingFunction[Apart[expr, n], n, x, opts];

GeneratingFunction[expr_ * (n_ + k_Integer?Positive)^(j_Integer?Negative), arg2, opts:OptionsPattern[]] := With[
    {t = Unique[]},
    x^(-k) * Integrate[t^(k-1) * GeneratingFunction[expr * (n + k)^(j + 1),
        n, t, opts], {t, 0, x}]
];

(* symbolic sums *)
GeneratingFunction[Sum[expr_, {i_, lb_, ub_}], arg2, opts:OptionsPattern[]] /;
    FreeQ[lb, n] && FreeQ[ub, n] := Sum[GeneratingFunction[expr, n, x, opts], 
        {i, lb, ub}];

(* different ways to set terms to 0 *)
GeneratingFunction[Boole[expr_] * fac_, arg2, opts:OptionsPattern[]] :=
	GeneratingFunction[Piecewise[{{fac, expr}}], n, x, opts];

GeneratingFunction[UnitStep[expr_] * fac_, arg2, opts:OptionsPattern[]] :=
	GeneratingFunction[Piecewise[{{fac, expr >= 0}}], n, x, opts];

GeneratingFunction[Piecewise[{{expr_, Divisible[n_, k_]}}], arg2, 
	opts:OptionsPattern[]] :=
	GeneratingFunction[Piecewise[{{expr, Mod[n, k] == 0}}], n, x, opts];

(* "multisection formula" *)
GeneratingFunction[Piecewise[{{expr_, Mod[n_, k_] == j_}}], arg2, 
	opts:OptionsPattern[]] /; FreeQ[k, n] :=
	With[{var = Unique[]},
		k^(-1) * Sum[Exp[-var*j*2*Pi*I/k] * GeneratingFunction[
			expr, n, Exp[var * 2 * Pi *I /k] * x, opts], 
			{var, 0, k-1}]
	];

Protect[Evaluate[protected]];

End[] 
EndPackage[]
