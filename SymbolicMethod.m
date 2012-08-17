(* Mathematica Package *)

BeginPackage["Genfunlib`SymbolicMethod`"]

Spec::usage = "";
SMPlus::usage = "";
SMTimes::usage = "";
SMSeq::usage = "";
SMCyc::usage = "";
SMSet::usage = "";
SMPointing::usage = "";
SMSub::usage = "";
SMMultiset::usage = "";
GFEqns::usage = "";
Cardinality::usage = "";
Restricted::usage = "";
ZClass::usage = "";
EClass::usage = "";

Begin["`Private`"] (* Begin Private Context *) 

(* ::Section:: *)
(* Input validation *)

validateSpec

nonTerminals[Spec[list_, _]] := Union[list[[All, 1]]];

validateSpecSyntax[spec:Spec[{(_ == _)...}, True|False]] := Module[
	{
		ok = True
	},
	blah
];

specSymbols = {seq, cyc, set, multiset, prod, sum, zClass, eClass};

atomClassQ[class_] := class === zClass || class === eClass;

expandSpec[spec_] :=
  spec //. {
     specPre___, 
     sym_ == con_[conPre___, expr_?(! (Head[#] === Symbol) &), 
       conPost___],
     specPost___
     } :> With[
     {name = Unique[]},
     {specPre,
      sym == con[conPre, name, conPost],
      name == expr,
      specPost
      }
     ];

valuation[spec_] := Module[
   {
    v,
    change = True
    },
   v[eClass] = 0; v[zClass] = 1;
   Map[(v[#] = Infinity) &, nonTerminals[spec]];
   While[change,
    change = False;
    Map[
     Switch[#[[2]],
       _Symbol,
       change = (v[#[[1]]] != (v[#[[1]]] = v[#[[2]]])) || change,
       _sum,
       change = (v[#[[1]]] != (v[#[[1]]] = Min @@ v /@ #[[2]])) || 
         change,
       _prod,
       change = (v[#[[1]]] != (v[#[[1]]] = Plus @@ v /@ #[[2]])) || 
         change,
       _seq | _set | _multiset, 
       change = (v[#[[1]]] != (v[#[[1]]] = 0)) || change,
       _cyc, 
       change = (v[#[[1]]] != (v[#[[1]]] = v @@ #[[2]])) || change
       ] &,
     spec];
    ];
   v
   ];

finiteValuationsQ[spec_, v_] := 
  Max[v /@ nonTerminals[spec]] < Infinity;

reducedQ[spec_, v_] := ! MatchQ[
    spec,
    {
     specPre___,
     a_ == con_[sym_?(v[#] == 0 &)],
     specPost___
     }];

(* throws out edges corresponding to a product where the other factor \
has nonzero valuation; includes atomic classes as vertices *)
makeGraph[spec_, v_] := spec /.
     {
      lhs_ == zClass -> Sequence[],
      lhs_ == eClass -> Sequence[],
      lhs_ == rhs_Symbol -> lhs \[DirectedEdge] rhs,
      lhs_ == prod[first_?(v[#] == 0 &), second_?(v[#] == 0 &)] ->
       {lhs \[DirectedEdge] first, lhs \[DirectedEdge] second},
      lhs_ == prod[first_?(v[#] > 0 &), second_?(v[#] == 0 &)] -> 
       lhs \[DirectedEdge] first,
      lhs_ == prod[first_?(v[#] == 0 &), second_?(v[#] > 0 &)] -> 
       lhs \[DirectedEdge] second,
      lhs_ == prod[__] -> Sequence[],
      lhs_ == con_[args__] :> (lhs \[DirectedEdge] # &) /@ {args}
      } // Flatten // Graph;

circularQ[spec_, v_] := ! AcyclicGraphQ[makeGraph[spec, v]];


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