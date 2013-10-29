(* Mathematica Package *)

BeginPackage["Genfunlib`GFeqn2rec`"]

$FullAnalytic::usage = "$FullAnalytic is True iff SeriesCoefficient should " <> 
    "assume that " <>
    "all subexpressions of the expression to be expanded are " <> 
    "analytic, when the " <> "expansion is around 0.";

Begin["`Private`"] 

protected = Unprotect[SeriesCoefficient];

$FullAnalytic = False;

(* what can usually be used as a variable, according to 
    ref/message/General/ivar *)
variablePattern = Except[_String | _?NumberQ | _Plus | _Times | 
    _Sum | _Product | _^_Integer];

arg2 = {x:variablePattern, 0, n_};

(* coefficients of negative or noninteger powers are 0 *)
SeriesCoefficient[_, arg2, opts:OptionsPattern[]] := Module[
    {},
    0 /; NumericQ[n] && (n < 0 || !IntegerQ[n]) && $FullAnalytic
];

(* addition *)
SeriesCoefficient[expr1_ + expr2_, arg2, opts:OptionsPattern[]] := 
    SeriesCoefficient[expr1, {x, 0, n}, opts] + SeriesCoefficient[expr2, 
    {x, 0, n}, opts];

(* scaling (can produce simpler expressions than general multiplication) *)
SeriesCoefficient[fac_ * expr_, arg2, opts:OptionsPattern[]] /; FreeQ[fac, x] && 
    !FreeQ[expr, x] := 
  fac * SeriesCoefficient[expr, {x, 0, n}, opts];

(* shifting (can produce simpler expressions than multiplication) *)
SeriesCoefficient[x_^(k_) * expr_, arg2, 
    opts:OptionsPattern[]] := Module[
    {},
    (
    Boole[n - k >= 0] * SeriesCoefficient[expr, 
        {x, 0, n - k}, opts]
    ) /; !FreeQ[expr, x] && $FullAnalytic && FreeQ[k, x]
];

(* multiplication *)
(* doesn't seem to interfere with things like E^x*1/(1-x) *)
SeriesCoefficient[expr1_ * expr2_, arg2, opts:OptionsPattern[]] := With[
   {
    iterator = Unique[]
   }, 
   Module[{
    newOpts = Sequence@@(DeleteCases[{opts}, Verbatim[Rule][Assumptions, _]] ~ Append ~ (Assumptions -> 
    OptionValue[Assumptions] && Element[iterator, Integers] && iterator >= 0))
   },
       Sum[SeriesCoefficient[expr1, {x, 0, iterator}, newOpts] 
        * SeriesCoefficient[expr2, {x, 0, n - iterator}, newOpts], 
        {iterator, 0, n}]
   ] /; !FreeQ[expr1, x] && !FreeQ[expr2, x] && $FullAnalytic
];


(* derivatives and integrals *)
SeriesCoefficient[Derivative[k_][a_Symbol][(j_:1) * x_], arg2, 
opts:OptionsPattern[]]  := 
    Pochhammer[n + 1, k] j^n SeriesCoefficient[a[x], {x, 0, n + k}, opts] /;
    Simplify[Implies[OptionValue[Assumptions], k > 0]] && FreeQ[j, x];

SeriesCoefficient[Derivative[0, k2_][a_Symbol][j_ * x_, expr_], arg2, 
opts:OptionsPattern[]] :=
    j^n SeriesCoefficient[Derivative[0, k2][a][x, expr], {x, 0, n}, opts] /;
    Simplify[Implies[OptionValue[Assumptions], k2 > 0]] && FreeQ[expr, x] &&
    FreeQ[j, x]; 

SeriesCoefficient[Derivative[k1_, 0][a_Symbol][expr_, j_ * x_], arg2, 
opts:OptionsPattern[]] :=
    j^n SeriesCoefficient[Derivative[k1, 0][a][expr, x], {x, 0, n}, opts] /;
    Simplify[Implies[OptionValue[Assumptions], k1 > 0]] && FreeQ[expr, x] &&
    FreeQ[j, x]; 

SeriesCoefficient[Derivative[k1_, k2_][a_Symbol][(j_:1) * x_, expr_], arg2, 
opts:OptionsPattern[]] := 
    Pochhammer[n + 1, k1] * j^n * SeriesCoefficient[
        Derivative[0, k2][a][x, expr], {x, 0, n + k1}, opts] /;
    Simplify[Implies[OptionValue[Assumptions], k1 > 0 && k2 >= 0]] && 
        FreeQ[expr, x] && FreeQ[j, x]; 

SeriesCoefficient[Derivative[k2_, k1_][a_Symbol][expr_, (j_:1) * x_], arg2, 
opts:OptionsPattern[]] := 
    Pochhammer[n + 1, k1] * j^n * SeriesCoefficient[
        Derivative[k2, 0][a][expr, x], {x, 0, n + k1}, opts] /;
    Simplify[Implies[OptionValue[Assumptions], k1 > 0 && k2 >= 0]] && 
        FreeQ[expr, x] && FreeQ[j, x]; 

SeriesCoefficient[Derivative[k1_, k2_][a_Symbol][(j_:1) * x_, (k_:1) * x_], 
arg2, opts:OptionsPattern[]] :=
    With[
    {iterator = Unique[], first = Unique[], second = Unique[]},
    (
    Sum[k^iterator * j^(n - iterator) * 
        Pochhammer[iterator + 1, k1] * Pochhammer[n - iterator + 1, k2] 
        * SeriesCoefficient[a[first, second], {first, 0, iterator + k1}, 
            {second, 0, n - iterator + k2}, opts], {iterator, 0, n}]
    ) /; $FullAnalytic &&
    Simplify[Implies[OptionValue[Assumptions], k1 >= 0 && k2 >= 0]] && 
        FreeQ[j, x] && FreeQ[k, x]; 
];

SeriesCoefficient[Integrate[expr_, 
    {t_, 0, x_}], arg2, opts:OptionsPattern[]] := Module[
        {},
    (
    Piecewise[{
            {n >= 1,
                (1/n) * SeriesCoefficient[expr /. t -> x, 
                {x, 0, n - 1}, opts]
            }
        }]
    ) /; $FullAnalytic
];

(* powers of functions *)
SeriesCoefficient[a_Symbol[args__]^(k_Integer?Positive), arg2, 
        opts:OptionsPattern[]] /; !FreeQ[{args}, x] := 
    SeriesCoefficient[
            Unevaluated[a[args] * a[args]^(k - 1)], 
            {x, 0, n}, opts
    ]; 

(* compositions *)
SeriesCoefficient[a_Symbol[k_ * x_], arg2, opts:OptionsPattern[]] /; 
    FreeQ[k, x] := k^n * SeriesCoefficient[a[x], {x, 0, n}, opts];

SeriesCoefficient[a_Symbol[(k_:1) * x_, (j_:1) * x_], arg2, 
    opts:OptionsPattern[]] := With[
    {iterator = Unique[], first = Unique[], second = Unique[]},
    (
    Sum[k^iterator * j^(n - iterator) * 
        SeriesCoefficient[a[first, second], {first, 0, iterator}, 
            {second, 0, n - iterator}, opts], {iterator, 0, n}]
    ) /; $FullAnalytic && FreeQ[k, x] && FreeQ[j, x]
];

SeriesCoefficient[a_Symbol[k_*x_, j_], arg2, opts:OptionsPattern[]] /; 
    FreeQ[j, x] && FreeQ[k, x] := 
    k^n SeriesCoefficient[a[x, j], {x, 0, n}, opts];
SeriesCoefficient[a_Symbol[j_, k_*x_], arg2, opts:OptionsPattern[]] /; 
    FreeQ[j, x] && FreeQ[k, x] := 
    k^n SeriesCoefficient[a[j, x], {x, 0, n}, opts];

(* misc *)
SeriesCoefficient[Sum[expr_, {i_, lb_, ub_}], arg2, opts:OptionsPattern[]] /;
    FreeQ[lb, x] && FreeQ[ub, x] :=
    Sum[SeriesCoefficient[expr, {x, 0, n}, opts], {i, lb, ub}];

SeriesCoefficient[expr_, {x:variablePattern, 0, n_}, iters__List, 
    opts:OptionsPattern[]] := 
    SeriesCoefficient[SeriesCoefficient[expr, {x, 0, n}, opts], iters, 
        opts];

Protect[Evaluate[protected]];

End[]
EndPackage[]
