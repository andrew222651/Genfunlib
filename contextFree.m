(* TODO: delete this file (after all useful code has been gleaned) *)

BeginPackage["Genfunlib`contextFree`"]

Begin["`Private`"] (* Begin Private Context *) 

grammar = {
   a -> a1 ** b | a2 ** c,
   b -> a2 ** b ** a2 | EmptyWord,
   c -> a3 | EmptyWord};

grammar2 = {
   a -> a1 ** a | a2 ** c,
   b -> a2 ** b ** a2 | EmptyWord,
   c -> a3 | EmptyWord};

grammar2GF[grammar_, indet_Symbol] := Module[
   {
    nonTerms = nonTerminals[grammar],
    ret = grammar /. Rule -> Equal
    },
   ret = Replace[ret, 
     sym_Symbol /; ! (sym === Equal || 
          sym === NonCommutativeMultiply || sym === Alternatives || 
          sym === EmptyWord || MemberQ[nonTerms, sym]) :> indet, 
     Infinity];
   ret = Replace[ret, 
     sym_Symbol /; MemberQ[nonTerms, sym] :> sym[indet], Infinity];
   ret = Replace[ret, Verbatim[Alternatives] :> Plus, Infinity, 
     Heads -> True];
   ret = Replace[ret, NonCommutativeMultiply :> Times, Infinity, 
     Heads -> True];
   ret = Replace[ret, EmptyWord :> 1, Infinity];
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
          sym === EmptyWord || MemberQ[nonTerms, sym]) :> zClass, 
     Infinity];
   ret = Replace[ret, Verbatim[Alternatives] :> sum, Infinity, 
     Heads -> True];
   ret = Replace[ret, NonCommutativeMultiply :> prod, Infinity, 
     Heads -> True];
   ret = Replace[ret, EmptyWord :> eClass, Infinity];
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

cflConcat[grammar1_, grammar2_] := Module[
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
         EmptyWord] :> (nonTerm_ -> initial2), 
       Verbatim[Alternatives][pre___, EmptyWord, post___] :> 
        Alternatives[pre, initial2, post]},
     grammar2 /. rules} // Flatten
   ];

cflStar[grammar1_] := Module[
   {
    initial1 = grammar1[[1, 1]]
    },
   Replace[
    grammar1, {Verbatim[Rule][nonTerm_, 
       EmptyWord] :> (nonTerm_ -> initial1 | EmptyWord), 
     Verbatim[Alternatives][pre___, EmptyWord, post___] :> 
      Alternatives[pre, EmptyWord, initial1, post]}, Infinity]
   ];
End[] (* End Private Context *)

EndPackage[]