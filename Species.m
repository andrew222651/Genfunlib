(* Mathematica Package *)

BeginPackage["Genfunlib`Species`"]

Begin["`Private`"] (* Begin Private Context *) 
(* ::Section:: *)
(* To GF eqns *)

(* simplifies Sum[generalTerm*Boole[pred[n]], {n, slb, sub}] *)
restrictedSum[generalTerm_, Function[GreaterEqual[ub_: Infinity, Slot[1], lb_: 0]], {n_, slb_, sub_}] := 
	Sum[generalTerm, {n, Max[slb, lb], Min[sub, ub]}];
	
restrictedSum[generalTerm_, Function[LessEqual[lb_: 0, Slot[1], ub_: Infinity]], {n_, slb_, sub_}] := 
	Sum[generalTerm, {n, Max[slb, lb], Min[sub, ub]}];
	
restrictedSum[generalTerm_, pred_, {n_, slb_, sub_}] := 
	Sum[Boole[pred[n]] * generalTerm, {n, slb, sub}];	

(* labeled *)                     
GFEqns[ spec:Spec[list_List, True], indet_Symbol ] := Module[
	{
		numAtomicClasses = Max @@ First /@ Cases[list, ZClass[n_], Infinity] //Max[0,#]&,
		nonTerms = nonTerminals[spec],
		indets,
		unique,
		ret = Hold[list]
	},
	(
	indets = Sequence @@ indet /@ Range[numAtomicClasses];
	
	ret = Replace[ret,
		{
			ZClass[n_] :> indet[n],
			EClass :> 1,
			sym_Symbol?(MemberQ[nonTerms, #1] &) :> sym[indets]
		}, 
		{1, Infinity}, Heads -> True
	];
	
	ret = FixedPoint[Function[iter, Replace[iter,
		{
			SMPlus[args__] :> Plus[args],
			SMTimes[args__] :> Times[args],
			
			SMSeq[arg_] :> 1 / (1 - arg),
			SMSeq[arg_, Cardinality -> pred_] :> (unique = Unique[];
				restrictedSum[arg^unique, pred, {unique, 0, Infinity}]),
			
			SMCyc[arg_] :> Log[ 1/(1 - arg) ],
			SMCyc[arg_, Cardinality -> pred_] :> (unique = Unique[];
				Boole[pred[0]] + restrictedSum[arg^unique / unique, pred, {unique, 1, Infinity}]),
			
			SMSet[arg_] :> Exp[arg],
			SMSet[arg_, Cardinality -> pred_] :> (unique = Unique[];
				restrictedSum[arg^unique / (unique!), pred, {unique, 0, Infinity}]),
			
			Restricted[expr_, {}] :> expr,
			Restricted[expr_, {param_ -> pred_, rest:((_) ...)}] :> (unique = Unique[];
				restrictedSum[
					SeriesCoefficient[Restricted[expr, {rest}], {indet[param], 0, unique}] * indet[param]^unique, 
					pred, {unique, 0, Infinity}
				]),
			
			SMPointing[expr_, param_] :> indet[param] * D[expr, indet[param]],
				
			SMSub[func_, arg_, param_] :> (func /. indet[param] :> arg)
			
		}, {1, Infinity}, Heads -> True
	]], ret]; 
		
	ReleaseHold[ret]	
			
	) /; validateSpec[Spec]
]; 

(* unlabeled *)
GFEqns[spec:Spec[list_List, False], indet_Symbol] := Module[
	{
		numAtomicClasses = Max @@ First /@ Cases[list, ZClass[n_], Infinity] //Max[0,#]&,
		nonTerms = nonTerminals[spec],
		indets,
		unique, uniqueAux,
		ret = Hold[list]
	},
	(
	indets = Sequence @@ indet /@ Range[numAtomicClasses];
	
	ret = Replace[ret,
		{
			ZClass[n_] :> indet[n],
			EClass :> 1,
			sym_Symbol?(MemberQ[nonTerms, #1] &) :> sym[indets]
		}, 
		{1, Infinity}, Heads -> True
	];
	
	ret = FixedPoint[Function[iter, Replace[iter,
		{
			SMPlus[args__] :> Plus[args],
			SMTimes[args__] :> Times[args],
			
			SMSeq[arg_] :> 1 / (1 - arg),
			SMSeq[arg_, Cardinality -> pred_] :> (unique = Unique[];
				restrictedSum[arg^unique, pred, {unique, 0, Infinity}]),
			
			SMCyc[arg_] :> (unique = Unique[];
				Sum[EulerPhi[unique]/unique * Log[1/(1 - (arg /. indet[n_] :> indet[n]^unique))], {unique, 1, Infinity}]),
			(* p. 730 *)
			SMCyc[arg_, Cardinality -> pred_] :> (unique = Unique[];
				restrictedSum[
					SeriesCoefficient[
						Sum[EulerPhi[unique]/unique * Log[1/(1 - uniqueAux^unique * (arg /. indet[n_] :> indet[n]^unique))], 
							{unique, 1, Infinity}
						],
						{uniqueAux, 0, unique}
					], 
					pred, 
					{unique, 0, Infinity}
				]
			),
			
			SMSet[arg_] :> (unique = Unique[];
				Exp@Sum[(-1)^(unique - 1)/unique * (arg /. indet[n_] :> indet[n]^unique), {unique, 1, Infinity}]),
			SMSet[arg_, Cardinality -> pred_] :> (unique = Unique[];
				restrictedSum[
					SeriesCoefficient[
						Exp@Sum[(-1)^(unique - 1)/unique * uniqueAux^unique * (arg /. indet[n_] :> indet[n]^unique), 
							{unique, 1, Infinity}
						],
						{uniqueAux, 0, unique}
					], 
					pred, 
					{unique, 0, Infinity}
				]
			),
			
			SMMultiset[arg_] :> (unique = Unique[];
				Exp@Sum[1/unique * (arg /. indet[n_] :> indet[n]^unique), {unique, 1, Infinity}]),
			SMMultiset[arg_, Cardinality -> pred_] :> (unique = Unique[];
				restrictedSum[
					SeriesCoefficient[
						Exp@Sum[1/unique * uniqueAux^unique * (arg /. indet[n_] :> indet[n]^unique), 
							{unique, 1, Infinity}
						],
						{uniqueAux, 0, unique}
					], 
					pred, 
					{unique, 0, Infinity}
				]
			),
			
			Restricted[expr_, {}] :> expr,
			Restricted[expr_, {param_ -> pred_, rest:((_) ...)}] :> (unique = Unique[];
				restrictedSum[
					SeriesCoefficient[Restricted[expr, {rest}], {indet[param], 0, unique}] * indet[param]^unique, 
					pred, {unique, 0, Infinity}
				]),
			
			SMPointing[expr_, param_] :> indet[param] * D[expr, indet[param]],
				
			SMSub[func_, arg_, param_] :> (func /. indet[param] :> arg)
			
		}, {1, Infinity}, Heads -> True
	]], ret]; 
		
	ReleaseHold[ret]	
			
	) /; validateSpec[Spec]
];


End[] (* End Private Context *)

EndPackage[]
