(* Mathematica Package *)

BeginPackage["Genfunlib`rec2GFeqn`"]

Begin["`Private`"] (* Begin Private Context *) 

protected = Unprotect[GeneratingFunction];

GeneratingFunction[n_^(k_) * f_[args__], n_, x_] /; !FreeQ[{args}, n] :=
	With[ {var = Unique[]},
		Sum[StirlingS2[k, var]*x^var*D[GeneratingFunction[
			f[args], n, x], {x, var}], {var, 1, k}]
];

GeneratingFunction[Sum[expr_, {i_, lb_, ub_}], n_, x_] :=
	Sum[GeneratingFunction[expr, n, x], {i, lb, ub}];

GeneratingFunction[expr_ / (n_ + 1), n_, x_] := x^(-1) * Integrate[
	GeneratingFunction[expr, n, x] /. x -> t, {t, 0, x}];

GeneratingFunction[f_[n_ + i_?Positive], n_, x_] := With[
	{var = Unique[]},
	( GeneratingFunction[f[n], n, x] - Sum[f[var]*x^var, {var, 0, i-1}]) *
		x^(-i)
];

GeneratingFunction[f_[n_ - i_?Positive], n_, x_] := 
	x^i * GeneratingFunction[f[n], n, x] + Sum[f[-j] * x^(i-j), {j, 1, i}];

GeneratingFunction[Boole[expr_] * fac_, n_, x_] :=
	GeneratingFunction[Piecewise[{{fac, expr}}], n, x];

GeneratingFunction[UnitStep[expr_] * fac_, n_, x_] :=
	GeneratingFunction[Piecewise[{{fac, expr >= 0}}], n, x];

GeneratingFunction[Piecewise[{{expr_, Divisible[n_, k_]}}], n_, x_] :=
	GeneratingFunction[Piecewise[{{expr, Mod[n, k] == 0}}], n, x];

(* "multisection formula" *)
GeneratingFunction[Piecewise[{{expr_, Mod[n_, k_] == j_}}], n_, x_] :=
	With[{var = Unique[]},
		k^(-1) * Sum[Exp[-var*j*2*Pi*I/k] * GeneratingFunction[
			expr, n, x],  /. x -> Exp[var * 2 * Pi *I /k*x]
			{var, 0, k-1}]
	];

Protect[Evaluate[protected]];

End[] (* End Private Context *)
EndPackage[]
