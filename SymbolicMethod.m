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
Cardinality::usage = "";
Restricted::usage = "";
ZClass::usage = "";
EClass::usage = "";
ToGenfunlibSpec::usage = "";

Begin["`Private`"] (* Begin Private Context *) 

(* ::Section:: *)
(* Syntactic input validation *)

validateRHS[sym_, nonTerms_] /; MemberQ[nonTerms, sym] := True;
validateRHS[EClass, _] := True;
validateRHS[ZClass[n_Integer?Positive] /; n >= 1, _] := True;

validateRHS[SMPlus[args__], nonTerms_] := And @@ validateRHS[#, nonTerms]& /@ {args};
validateRHS[SMTimes[args__], nonTerms_] := And @@ validateRHS[#, nonTerms]& /@ {args};

validateRHS[SMSeq[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMSeq[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMCyc[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMCyc[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMSet[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMSet[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMMultiset[arg_], nonTerms_] := validateRHS[arg, nonTerms];
validateRHS[SMMultiset[arg_, Cardinality -> pred_], nonTerms_] := validateRHS[arg, nonTerms] && validatePred[pred];

validateRHS[SMSub[first_, second_, paramNumber_Integer?Positive], nonTerms_] := validateRHS[first, nonTerms] && validateRHS[second, nonTerms];
validateRHS[SMPointing[arg_, paramNumber_Integer?Positive], nonTerms] := validateRHS[arg, nonTerms];

validateRHS[Restricted[arg_, rules:{(_Integer?Positive -> _)...}], nonTerms] := Module[
	{
		integers = rules[[All, 1]],
		preds = rules[[All, 2]]
	},
	(Length@integers == Length@Union@integers) && And @@ validatePred /@ preds && validatRHS[arg, nonTerms]
];

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
	
	ok
];
validateSpecSyntax[___] := False;

(* ::Section:: *)
(* Semantic input validation *)

nonTerminals[Spec[list_, _]] := list[[All, 1]];

(* returns true if... *)
(* returns conditions under which input is semantically valid *)
validateSpecSemantics

validateSpec[spec_] := validateSpecSyntax[spec];

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
  		(head : (SMSet | SMSeq | SMCyc))[arg_, rel_[card, k_]] :> 
   			head[arg, Cardinality -> (rel[#, k] &)],
  		(head : (SMSet | SMSeq | SMCyc))[arg_, rel_[k_, card]] :> 
   			head[arg, Cardinality -> (rel[k, #] &)]
  		},
 		{0, Infinity}];
 	
 	Spec[ret//ReleaseHold, labeled]
];                               
                                          
End[] (* End Private Context *)

EndPackage[]
