(* Mathematica Package *)

BeginPackage["Genfunlib`SymbolicMethod`"]

Spec::usage = "Spec[{lhs1 ==  rhs1, ...}, labeled] is a combinatorial " <>
    "specification.";
SMPlus::usage = "SMPlus is the addition construction from the symbolic method.";
SMTimes::usage = "SMTimes is the multiplication construction from the " <>
    "symbolic method.";
SMSeq::usage = "SMSeq is the sequence construction from the symbolic method.";
SMCyc::usage = "SMCyc is the cycle construction from the symbolic method.";
SMSet::usage = "SMSet is the set construction from the symbolic method.";
SMPointing::usage = "SMPointing is the pointing construction from the " <> 
    "symbolic method.";
SMSub::usage = "SMSub is the substitution construction from the symbolic " <>
    "method.";
SMMultiset::usage = "SMMultiset is the multiset construction from the " <>
    "symbolic method.";
Cardinality::usage = "Cardinality is an option for symbolic method " <>
    "constructions which takes a Function on the integers with which to" <>
    "restrict the construction.";
Restricted::usage = "Restricted[class, pred] is the class of objects from " <>
    "class with sizes in pred^(-1)(True).";
ZClass::usage = "ZClass[n] is the nth atomic class.";
EClass::usage = "EClass is the epsilon class.";
ToGenfunlibSpec::usage = "ToGenfunlibSpec[mapleString, labeled] converts " <>
    "from Combstruct to Genfunlib combinatorial specification syntax.";
ToGFEqns::usage = "ToGFEqns[spec, indeterminate] gives the system of power " <>
    "series equations corresponding to spec, using the given indeterminate." 

Begin["`Private`"] (* Begin Private Context *) 

(* ::Section:: *)
(* Syntactic input validation *)

Spec::invalid = "Invalid specification.";

validatePred[_Function] := True;
validatePred[___] := False;

validateRHS[sym_, nonTerms_] /; MemberQ[nonTerms, sym] := True;
validateRHS[EClass, _] := True;
validateRHS[ZClass[n_Integer?Positive], _] := True;

validateRHS[SMPlus[args__], nonTerms_] := And @@ (validateRHS[#, nonTerms]& /@ {args});
validateRHS[SMTimes[args__], nonTerms_] := And @@ (validateRHS[#, nonTerms]& /@ {args});

validateRHS[SMSeq[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMSeq[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMCyc[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMCyc[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMSet[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMSet[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMMultiset[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMMultiset[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMSub[first_, second_], nonTerms_] := validateRHS[first, nonTerms] && validateRHS[second, nonTerms];
validateRHS[SMPointing[arg_], nonTerms] := validateRHS[arg, nonTerms];

validateRHS[Restricted[arg_, pred_], nonTerms] := validatePred[pred] && validateRHS[arg, nonTerms];

validateRHS[___] := False;

validateSpecSyntax[spec:Spec[list:{HoldPattern[_ == _]..}, labeled:True|False]] := Module[
	{
		ok = True,
		lhss = list[[All, 1]],
		rhss = list[[All, 2]]
	},
	ok = ok && MatchQ[lhss, {(_Symbol|(_Symbol)[_Integer])...}];
	ok = ok && Length@lhss == Length@Union@lhss;
	If[labeled && MemberQ[list, SMMultiset, {0, Infinity}, Heads -> True], ok = False];  
	ok = ok && And @@ (validateRHS[#, lhss]& /@ rhss);
	
    If[ !ok, Message[Spec::invalid]];
	ok
];
validateSpecSyntax[___] := False;

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
ToGFEqns[ spec:Spec[list_List, True], indet_Symbol ] := Module[
	{
		numAtomicClasses = Max @@ First /@ Cases[list, ZClass[n_], Infinity] //Max[0,#]&,
		nonTerms = list[[All, 1]],
		indets,
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
			SMSeq[arg_, Cardinality -> pred_] :> With[{unique = Unique[]},
				restrictedSum[arg^unique, pred, {unique, 0, Infinity}]],
			
			SMCyc[arg_] :> Log[ 1/(1 - arg) ],
			SMCyc[arg_, Cardinality -> pred_] :> With[{unique = Unique[]},
				Boole[pred[0]] + restrictedSum[arg^unique / unique, pred, {unique, 1, Infinity}]],
			
			SMSet[arg_] :> Exp[arg],
			SMSet[arg_, Cardinality -> pred_] :> With[{unique = Unique[]},
				restrictedSum[arg^unique / (unique!), pred, {unique, 0, Infinity}]],
			
			Restricted[expr_, {}] :> expr,
			Restricted[expr_, pred_] :> With[{unique = Unique[]},
				restrictedSum[
					SeriesCoefficient[expr, {indet[1], 0, unique}] * indet[1]^unique, 
					pred, {unique, 0, Infinity}
				]],
			
			SMPointing[expr_] :> indet[1] * D[expr, indet[1]],
				
			SMSub[func_, arg_] :> (func /. indet[1] :> arg)
			
		}, {1, Infinity}, Heads -> True
	]], ret]; 
		
	ReleaseHold[ret]	
			
	) /; validateSpecSyntax[spec]
]; 

(* unlabeled *)
ToGFEqns[spec:Spec[list_List, False], indet_Symbol] := Module[
	{
		numAtomicClasses = Max @@ First /@ Cases[list, ZClass[n_], Infinity] //Max[0,#]&,
		nonTerms = list[[All, 1]],
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
			SMSeq[arg_, Cardinality -> pred_] :> With[{unique = Unique[]},
				restrictedSum[arg^unique, pred, {unique, 0, Infinity}]],
			
			SMCyc[arg_] :> With[{unique = Unique[]},
				Sum[EulerPhi[unique]/unique * Log[1/(1 - (arg /. indet[n_] :> indet[n]^unique))], {unique, 1, Infinity}]],
			(* p. 730 *)
			SMCyc[arg_, Cardinality -> pred_] :> With[{unique = Unique[], 
                uniqueAux = Unique[]},
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
			],
			
			SMSet[arg_] :> With[{unique = Unique[]},
				Exp@Sum[(-1)^(unique - 1)/unique * (arg /. indet[n_] :> indet[n]^unique), {unique, 1, Infinity}]],
			SMSet[arg_, Cardinality -> pred_] :> With[{unique = Unique[], 
                uniqueAux = Unique[]},
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
			],
			
			SMMultiset[arg_] :> With[{unique = Unique[]},
				Exp@Sum[1/unique * (arg /. indet[n_] :> indet[n]^unique), {unique, 1, Infinity}]],
			SMMultiset[arg_, Cardinality -> pred_] :> With[{unique = Unique[],
                uniqueAux = Unique[]},
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
			],
			
			Restricted[expr_, {}] :> expr,
			Restricted[expr_, param_] :> With[{unique = Unique[]},
				restrictedSum[
					SeriesCoefficient[expr, {indet[1], 0, unique}] * indet[1]^unique, 
					pred, {unique, 0, Infinity}
				]],
			
			SMPointing[expr_] :> indet[1] * D[expr, indet[1]],
				
			SMSub[func_, arg_] :> (func /. indet[1] :> arg)
			
		}, {1, Infinity}, Heads -> True
	]], ret]; 
		
	ReleaseHold[ret]	
			
	) /; validateSpecSyntax[spec]
];

(* ::Section:: *)
(* Combstruct grammar to Genfunlib spec *)

(* assumes there are no parenthesis except to group function arguments *)
(* assumes nonterminals are only one character *)
(* assumes the grammar is explicit *)
ToGenfunlibSpec[str_String, labeled:(True|False)] := Module[
	{
		ret = str
	},
	ret = StringReplace[ret, c_?UpperCaseQ :> ToLowerCase[c] <> ToLowerCase[c]];
	ret = StringReplace[ret, {
  		" = " -> " == ",
  		"(" -> "[", ")" -> "]",
  		"pprod" -> "SMTimes",
  		"uunion" -> "SMPlus",
  		"sset" -> "SMSet",
  		"ppowersset" -> "SMSet",
  		"ccycle" -> "SMCyc",
  		"ssubst" -> "SMSub",
  		"ssequence" -> "SMSeq",
  		"zz" -> "ZClass[1]",
  		"aatom" -> "ZClass[1]",
  		"eepsilon" -> "EClass"
  	}];
  	ret = ToExpression[ret, InputForm, Hold];
  	ret = Replace[ret, 
 		SMSub[first_, second_] :> SMSub[second, first], {0, Infinity}];
 	ret = Replace[ret, {
  		(head : (SMSet | SMSeq | SMCyc))[arg_, rel_[Global`card, k_]] :> 
   			head[arg, Cardinality -> (rel[#, k] &)],
  		(head : (SMSet | SMSeq | SMCyc))[arg_, rel_[k_, Global`card]] :> 
   			head[arg, Cardinality -> (rel[k, #] &)]
  		},
 		{0, Infinity}];
 	
 	Spec[ret//ReleaseHold, labeled]
];                               

ToGFEqns::invalidArgumentSyntax = "Invalid argument syntax.";
ToGenfunlibSpec::invalidArgumentSyntax = "Invalid argument syntax.";
ToGFEqns[___] /; (Message[ToGFEqns::invalidArgumentSyntax]; False) := Null;
ToGenfunlibSpec[___] /; (Message[ToGenfunlibSpec::invalidArgumentSyntax]; False) := Null;

End[] (* End Private Context *)

EndPackage[]
