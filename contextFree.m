(* Mathematica Package *)

BeginPackage["contextFree`"]
(* Exported symbols added here with SymbolName::usage *)  

Begin["`Private`"] (* Begin Private Context *) 
Protect[EmptyString];

grammar = {
   a -> a1 ** b | a2 ** c,
   b -> a2 ** b ** a2 | EmptyString,
   c -> a3 | EmptyString};

grammar2 = {
   a -> a1 ** a | a2 ** c,
   b -> a2 ** b ** a2 | EmptyString,
   c -> a3 | EmptyString};

(* name conflict with alas.nb: *)
nonTerminals[grammar_] := (grammar /. Rule -> List)[[All, 1]];

grammar2GF[grammar_, indet_Symbol] := Module[
   {
    nonTerms = nonTerminals[grammar],
    ret = grammar /. Rule -> Equal
    },
   ret = Replace[ret, 
     sym_Symbol /; ! (sym === Equal || 
          sym === NonCommutativeMultiply || sym === Alternatives || 
          sym === EmptyString || MemberQ[nonTerms, sym]) :> indet, 
     Infinity];
   ret = Replace[ret, 
     sym_Symbol /; MemberQ[nonTerms, sym] :> sym[indet], Infinity];
   ret = Replace[ret, Verbatim[Alternatives] :> Plus, Infinity, 
     Heads -> True];
   ret = Replace[ret, NonCommutativeMultiply :> Times, Infinity, 
     Heads -> True];
   ret = Replace[ret, EmptyString :> 1, Infinity];
   ret
   ];

grammar2spec[grammar_] := Module[
   {
    nonTerms = nonTerminals[grammar],
    ret = grammar /. Rule -> Equal
    },
   ret = Replace[ret, 
     sym_Symbol /; ! (sym === Equal || 
          sym === NonCommutativeMultiply || sym === Alternatives || 
          sym === EmptyString || MemberQ[nonTerms, sym]) :> zClass, 
     Infinity];
   ret = Replace[ret, Verbatim[Alternatives] :> sum, Infinity, 
     Heads -> True];
   ret = Replace[ret, NonCommutativeMultiply :> prod, Infinity, 
     Heads -> True];
   ret = Replace[ret, EmptyString :> eClass, Infinity];
   ret
   ];

cflUnion[grammar1_, grammar2_] := Module[
   {
    nonTerms1 = nonTerminals[grammar1],
    nonTerms2 = nonTerminals[grammar2],
    initial1, initial2,
    commonNonTerms,
    replacements,
    rules
    },
   commonNonTerms = nonTerms1 \[Intersection] nonTerms2;
   replacements = Unique /@ commonNonTerms;
   rules = MapThread[Rule, {commonNonTerms, replacements}];
   initial1 = grammar1[[1, 1]];
   initial2 = grammar2[[1, 1]] /. rules;
   {Unique[] -> initial1 | initial2, grammar1, grammar2 /. rules} // 
    Flatten
   ];

cflReversal[grammar_] := 
  grammar /. 
   NonCommutativeMultiply[args__] :> 
    NonCommutativeMultiply @@ Reverse@{args};

cflConcatenation[grammar1_, grammar2_] := Module[
   {
    nonTerms1 = nonTerminals[grammar1],
    nonTerms2 = nonTerminals[grammar2],
    initial2,
    commonNonTerms,
    replacements,
    rules
    },
   commonNonTerms = nonTerms1 \[Intersection] nonTerms2;
   replacements = Unique /@ commonNonTerms;
   rules = MapThread[Rule, {commonNonTerms, replacements}];
   initial2 = grammar2[[1, 1]] /. rules;
   {grammar1 /. {Verbatim[Rule][nonTerm_, 
         EmptyString] :> (nonTerm_ -> initial2), 
       Verbatim[Alternatives][pre___, EmptyString, post___] :> 
        Alternatives[pre, initial2, post]},
     grammar2 /. rules} // Flatten
   ];

cflStar[grammar1_] := Module[
   {
    initial1 = grammar1[[1, 1]]
    },
   Replace[
    grammar1, {Verbatim[Rule][nonTerm_, 
       EmptyString] :> (nonTerm_ -> initial1 | EmptyString), 
     Verbatim[Alternatives][pre___, EmptyString, post___] :> 
      Alternatives[pre, EmptyString, initial1, post]}, Infinity]
   ];
End[] (* End Private Context *)

EndPackage[]