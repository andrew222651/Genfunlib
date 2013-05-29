(* Mathematica Package *)

BeginPackage["Genfunlib`rec2GFeqn`"]

Begin["`Private`"] (* Begin Private Context *) 

protected = Unprotect[GeneratingFunction];

GeneratingFunction[n_^(k_) * f_[args__], n_, x_, opts:OptionsPattern[]] :=
	With[ {var = Unique[]},
		Sum[StirlingS2[k, var]*x^var*D[GeneratingFunction[
			f[args], n, x, opts], {x, var}], {var, 1, k}]
]/; !FreeQ[{args}, n] && FreeQ[k, n] && Simplify@Implies[OptionValue[
	Assumptions], Element[k, Integers] && k > 0];

GeneratingFunction[Sum[expr_, {i_, lb_, ub_}], n_, x_, opts:OptionsPattern[]] :=
	Sum[GeneratingFunction[expr, n, x, opts], {i, lb, ub}];

GeneratingFunction[expr_ / (n_ + 1), n_, x_, opts:OptionsPattern[]] := x^(-1) * 
Integrate[
	GeneratingFunction[expr, n, t, opts], {t, 0, x}];

GeneratingFunction[f_[n_ + i_], n_, x_, opts:OptionsPattern[]] := With[
	{var = Unique[]},
	( GeneratingFunction[f[n], n, x, opts] - Sum[f[var]*x^var, 
	{var, 0, i-1}]) * x^(-i)
] /; Simplify@Implies[OptionValue[Assumptions], i > 0];

GeneratingFunction[f_[n_ - i_], n_, x_, opts:OptionsPattern[]] := 
	x^i * GeneratingFunction[f[n], n, x, opts] + 
	Sum[f[-j] * x^(i-j), {j, 1, i}] /; 
	Simplify@Implies[OptionValue[Assumptions], i > 0];

GeneratingFunction[Boole[expr_] * fac_, n_, x_, opts:OptionsPattern[]] :=
	GeneratingFunction[Piecewise[{{fac, expr}}], n, x, opts];

GeneratingFunction[UnitStep[expr_] * fac_, n_, x_, opts:OptionsPattern[]] :=
	GeneratingFunction[Piecewise[{{fac, expr >= 0}}], n, x, opts];

GeneratingFunction[Piecewise[{{expr_, Divisible[n_, k_]}}], n_, x_, 
	opts:OptionsPattern[]] :=
	GeneratingFunction[Piecewise[{{expr, Mod[n, k] == 0}}], n, x, opts];

(* "multisection formula" *)
GeneratingFunction[Piecewise[{{expr_, Mod[n_, k_] == j_}}], n_, x_, 
	opts:OptionsPattern[]] :=
	With[{var = Unique[]},
		k^(-1) * Sum[Exp[-var*j*2*Pi*I/k] * GeneratingFunction[
			expr, n, Exp[var * 2 * Pi *I /k] * x, opts], 
			{var, 0, k-1}]
	];

Protect[Evaluate[protected]];

End[] (* End Private Context *)
EndPackage[]
