(* Mathematica Package *)

BeginPackage["genfunlib`regular`"]

Protect[or, concat, star, NFA, DFA, RRGrammar, Regex, Digraph];
SetAttributes[concat, Flat];
SetAttributes[or, Flat];

Begin["`Private`"] (* Begin Private Context *) 

nonTerminals[RRGrammar[grammar_]] := (grammar /. Rule -> List)[[All, 1]];

validateNFA[NFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
	initialState_]] := Module[
	{
		ok = True
	},
	ok = ok && Head[numStates] === Integer && numStates >= 0;
	ok = ok && MatchQ[alphabet, {__String}] && !MemberQ[alphabet, ""];
	ok = ok && (numStates == 0 || MatrixQ[transitionMatrix, MatchQ[#, {___Integer}] && 
		(Max[#] <= numStates && Min[#] >= 1) &]);
	ok = ok && (numStates == 0 || Dimensions[transitionMatrix, 2] == {numStates, Length[alphabet] + 1});
	ok = ok && MatchQ[acceptStates, {___Integer}] && (numStates == 0 || 
		(Max[acceptStates] <= numStates && Min[acceptStates] >= 1));
	ok = ok && (numStates == 0 || (Head[initialState] === Integer && 1 <= initialState <= numStates));
	ok
];
validateNFA[_] := False;
	
validateDFA[DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
	initialState_]] := Module[
	{
		ok = True
	},
	ok = ok && Head[numStates] === Integer && numStates >= 0;
	ok = ok && MatchQ[alphabet, {__String}] && !MemberQ[alphabet, ""];
	ok = ok && (numStates == 0 || MatrixQ[transitionMatrix, Head[#] === Integer && 
		(# <= numStates && # >= 1) &]);
	ok = ok && (numStates == 0 || Dimensions[transitionMatrix, 2] == {numStates, Length[alphabet]});
	ok = ok && MatchQ[acceptStates, {___Integer}] && (numStates == 0 || 
		(Max[acceptStates] <= numStates && Min[acceptStates] >= 1));
	ok = ok && (numStates == 0 || (Head[initialState] === Integer && 1 <= initialState <= numStates));
	ok
];
validateDFA[_] := False;

validateStringRegex[RegularExpression[regex_String]] := Module[
	{
		ok = True
	},
	ok = ok && StringMatchQ[regex, (LetterCharacter | DigitCharacter | "\\*" | "(" | 
    ")" | "|") ...];
    ok = ok && Check[StringMatchQ["", regex], $Failed] != $Failed;
    ok
];   
validateStringRegex[_] := False;

validateSymbolicRegex[Regex[EmptyWord]] := True;
validateSymbolicRegex[Regex[str_String /; str != ""]] := True;
validateSymbolicRegex[Regex[star[regex_]]] := validateSymbolicRegex[Regex[regex]];
validateSymbolicRegex[Regex[or[regexes__]]] := And @@ validateSymbolicRegex /@ Regex /@ {regexes};
validateSymbolicRegex[Regex[concat[regexes__]]] := And @@ validateSymbolicRegex /@ Regex /@ {regexes};
validateSymbolicRegex[_] := False;

validateRRGrammar[RRGrammar[grammar:{(_ -> _) ...}]] := Module[
	{
		ok = True,
		nonTerms = nonTerminals[grammar],
		validateTerm
	},
	ok = ok && MatchQ[nonTerms, {(_Symbol | _Symbol[_Integer]) ...}];
	
	validateTerm[EmptyWord] := True;
	validateTerm[sym_Symbol /; MemberQ[nonTerms, sym]] := True;
	validateTerm[sym_Symbol[n_Integer] /; MemberQ[nonTerms, sym[n]]] := True;
	validateTerm[str_String /; str != ""] := True;
	validateTerm[concat[str_String /; str != "", sym_Symbol /; MemberQ[nonTerms, sym]]] := True;
	validateTerm[ concat[str_String /; str != "", sym_Symbol[n_Integer] /; MemberQ[nonTerms, sym[n]]] ] := True;
	validateTerm[_] := False;
	
	ok = ok && MatchQ[grammar[[All,2]], {( _?validateTerm | or[ _?validateTerm .. ]) ...}];
	
	ok
];
validateRRGrammar[_] := False;

validateDigraph[Digraph[graph_, startVertices_List, endVertices_List, eAccepted_]] := Module[
	{
		ok = True,
		vertices
	},
	(* validate graph *)
	ok = ok && (EmptyGraphQ[graph] || DirectedGraphQ[graph]);
	vertices = VertexList[graph];
	ok = ok && MatchQ[vertices, {___Integer}];
	ok = ok && And @@ ( (Head[PropertyValue[{graph, #}, VertexLabels]] === String && 
		PropertyValue[{graph, #}, VertexLabels] != "") & /@ vertices );
	(* validate vertex lists *)
	ok = ok && Union[startVertices, endVertices, vertices] == Union[vertices];
	(* validate eAccepted *)
	ok = ok && ( (eAccepted === True) || (eAccepted === False) );
	
	ok
];
validateDigraph[_] := False;

(* http://en.wikipedia.org/wiki/DFA_minimization#Hopcroft \
.27s_algorithm *)
hopcroft[DFA[0, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_]] := 
  DFA[0, alphabet, transitionMatrix, acceptStates, initialState];

hopcroft[DFA[numStates_, alphabet_, transitionMatrix_, {}, 
    initialState_]] := 
  DFA[0, alphabet, transitionMatrix, {}, initialState];

hopcroft[DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_]] := Module[
   {
    p = {Sort@acceptStates, 
      Complement[Range[numStates], acceptStates]},
    w = {Sort@acceptStates}, a, c, x
    },
   While[Length[w] > 0,
    a = First[w]; w = Delete[w, 1];
    For[c = 1, c <= Length[alphabet], c++,
     x = Flatten@
       Position[transitionMatrix[[All, c]], 
        _?(MemberQ[a, #] &), {1}, Heads -> False];
     Map[
      (
        p = 
         Union[p /. # :> 
            Sequence[Intersection[x, #], Complement[#, x]]];
        If[MemberQ[w, #],
         w = 
          Union[w /. # :> 
             Sequence[Intersection[x, #], Complement[#, x]]],
         (* else *)
         If[Length[Intersection[x, #]] <= Length[Complement[#, x]],
          w = Union[w, {Intersection[x, #]}],
          (* else *)
          w = Union[w, {Complement[#, x]}]
          (* end else *)
          ]
         (* end else *)
         ]
        ) &,
      Select[p, Intersection[#, x] != {} &]
      ];
     ];
    ];
   p = DeleteCases[p, {}];
   DFA[
    Length[p],
    alphabet,
    Table[
     First@Flatten@
       Position[
        p, _?(MemberQ[#, transitionMatrix[[First@p[[s]], c]]] &), {1},
         Heads -> False], {s, 1, Length[p]}, {c, 1, Length[alphabet]}],
    Flatten@
     Position[p, _?(Intersection[#, acceptStates] != {} &), {1}, 
      Heads -> False],
    First@
     Flatten@Position[p, _?(MemberQ[#, initialState] &), {1}, 
       Heads -> False]
    ]
];

(* http://en.wikipedia.org/wiki/DFA_minimization# Unreachable_states *)
removeUnreachables[
   DFA[0, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_]] := 
  DFA[0, alphabet, transitionMatrix, {}, initialState];

removeUnreachables[
   DFA[numStates_, alphabet_, transitionMatrix_, {}, initialState_]] :=
   DFA[0, alphabet, transitionMatrix, {}, initialState];

(* DFA with some states, some of which are accepting states *)
removeUnreachables[
   DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_]] := Module[
   {
    reachables = {initialState}, newStates = {initialState},
    temp, unreachables,
    unreachable,
    newTransitionMatrix = transitionMatrix, 
    newInitialState = initialState, newNumStates = numStates, 
    newAcceptStates = acceptStates
    },
   (* determine unreachables *)
   While[newStates != {},
    temp = Union@Flatten@transitionMatrix[[newStates, All]];
    newStates = Complement[temp, reachables];
    reachables = Union[reachables, newStates];
    ];
   unreachables = Reverse@Complement[Range[numStates], reachables];
   
   (* delete unreachables *)
   While[unreachables != {},
    (* take the greatest unreachable *)
    unreachable = First@unreachables; 
    unreachables = Delete[unreachables, 1];
    newNumStates -= 1;
    newTransitionMatrix = Delete[newTransitionMatrix, unreachable];
    newAcceptStates = DeleteCases[newAcceptStates, unreachable];
    newTransitionMatrix = 
     newTransitionMatrix /. 
      state_Integer /; unreachable + 1 <= state <= newNumStates + 1 :>
        state - 1;
    newInitialState = 
     newInitialState /. 
      state_Integer /; unreachable + 1 <= state <= newNumStates + 1 :>
        state - 1;
    newAcceptStates = 
     newAcceptStates /. 
      state_Integer /; unreachable + 1 <= state <= newNumStates + 1 :>
        state - 1;
    ];
   
   DFA[newNumStates, alphabet, newTransitionMatrix, newAcceptStates, 
    newInitialState]
];

(* transitions is a matrix like \
http://en.wikipedia.org/wiki/Finite-state_machine # State \
.2FEvent_table *)
(* markers is a list of {{j,k},letter,marker}, where the transition \
to be marked is from j to k with letter letter, and the indeterminate \
marking the number of them is marker *)
dfa2gf[{numStates_Integer, alphabetSize_, transitions_, 
     acceptingStates_, initialState_} indet_, markers_: {}] := Module[
   {
    t,
    v = {Table[Boole[MemberQ[acceptingStates, i]], {i, 1, numStates}]}
    },
   t = Table[
     Count[transitions[[j]], k], {j, 1, numStates}, {k, 1, numStates}];
   markers /. {{j_, k_}, letter_, 
      marker_} :> (Part[t, j, k] += -1 + marker);
   (Inverse[IdentityMatrix[numStates] - indet*t].(v\[Transpose]))[[
    initialState, 1]]
   ];

(* transfer-matrix *)

(* markers is a list of {{j,k},marker}, where the transition to be \
marked is from j to k and the indeterminate marking the number of \
them is marker *)
(* part i,j of the returned matrix is the GF for the number of walks \
starting at i and ending at j, with the markers marking the number of \
their transitions *)
transferMatrix[matrix_, indet_, markers_: {}] := Module[{t = matrix},
   markers /. {{j_, k_}, marker_} :> (Part[t, j, k] += -1 + marker);
   Inverse[IdentityMatrix[Length[matrix]] - indet*matrix]
   ];

(* unambiguous regex *)

(* TODO: test for ambiguity *)
(* TODO: convert DFA to unambiguous regex *)
(* TODO: issue: "a**" causes problems *)
regex2GF[RegularExpression[string_String], indet_Symbol] := 
  parsedRegex2GF[pars[string], indet];
regex2GF[string_String, indet_Symbol] := 
  parsedRegex2GF[pars[string], indet];

parsedRegex2GF[parsed_, indet_] := (parsed //.
     letter[n_] :> indet) //. {
    or[args__] :> Plus[args],
    concat[args__] :> Times[args],
    star[arg_] :> 1/(1 - arg)
    };

(* crappy: "," not allowed in the regex *)

pars[regex_] := Module[
   {
    temp
    },
   temp = 
    FixedPoint[
     StringReplace[#, 
       a_ ~~ b_ /; 
         a != "(" && b != ")" && b != "*" && a != "," && b != "," && 
          a != "|" && b != "|" :> a ~~ "," ~~ b] &, regex];
   temp = StringReplace[temp, "*" -> "^2"];
   temp = StringReplace[temp, "," -> "**"];
   temp = ToExpression[temp, InputForm, Hold];
   temp = temp //. Power[expr_, 2] :> star[expr];
   temp = temp //. NonCommutativeMultiply[args__] :> concat[args];
   temp = temp //. Verbatim[Alternatives][args__] :> or[args];
   sym2integers[temp]
   ];

Protect[letter];

sym2integers[parsed_] := Module[
   {
    alphabet = 
     Cases[parsed, 
       sym_Symbol?(! MemberQ[{Hold, or, concat, star}, #] &) :> 
        Hold[sym], Infinity] // Union,
    f,
    new
    },
   SetAttributes[f, HoldFirst];
   f[arg_] := MemberQ[alphabet, Hold[arg]];
   new = ReleaseHold[
     Replace[parsed, sym_Symbol?f :> Hold[sym], Infinity]];
   new = new //. 
     h : Hold[sym_Symbol?f] :> 
      letter[Position[alphabet, h] // First // First];
   new
   ];

(* multivariate unambiguous regex *)
(* regex is in expression format, using or, concat and star *)
(* characters are strings and have size one *)
(* subregexes can be enclosed in a 'tag' expression with a second \
argument which is the indeterminate to tag (occurrences of) that \
subregex with *)



taggedRegex2GF[regex_, indet_] := regex //. {
   string_String :> indet,
   tag[first_, second_] :> first*second,
   or[args__] :> Plus[args],
   concat[args__] :> Times[args],
   star[args__] :> 1/(1 - args)}

(* NFA to DFA *)

(* transitions is transpose of a matrix like \
n, 
with one extra col at the end for e-moves *)

(* possible bug: states that are within e-moves from end states must be considered end states, too; e.g. (start) --e--> (end) *)

nfa2dfa[{numStates_Integer, alphabetSize_Integer, transitionMatrix_, 
    acceptStates_?VectorQ, initialState_}] := Module[
   {
    dfaStateSet = Subsets[Range[numStates]],
    dfatransitionMatrix,
    dfaAcceptStates,
    dfaInitialState,
    ajacency = Table[
      ReplacePart[ConstantArray[False, numStates], 
       List /@ (transitionMatrix[[k, alphabetSize + 1]]) -> True],
      {k, 1, numStates}
      ]
    },
   floydWarshall[ajacency];
   dfaInitialState = 
    Position[
       dfaStateSet, {initialState, 
          Position[ajacency[[initialState]], True]} // Flatten // 
        Union] // First // First;
   dfaAcceptStates = 
    Map[(Position[dfaStateSet, #] // First // First) &, 
     Sort@Select[
       dfaStateSet, ((# \[Intersection] acceptStates) != {}) &]];
   dfatransitionMatrix = 
    makeTransitionMatrix[alphabetSize, dfaStateSet, transitionMatrix, 
     ajacency];
   {2^numStates, alphabetSize, dfatransitionMatrix, dfaAcceptStates, 
    dfaInitialState}
   ];

makeTransitionMatrix[alphabetSize_, dfaStateSet_, transitionMatrix_, 
  ajacency_] := Table[
   Map[stateSubset \[Function]
     Position[dfaStateSet,
        Map[state \[Function]
            {transitionMatrix[[state, i]], 
             Map[Position[ajacency[[#]], True] &, 
              transitionMatrix[[state, i]]]}, stateSubset] // 
          Flatten // Union] // First // First,
    dfaStateSet
    ],
   {i, 1, alphabetSize}
   ] // Transpose

SetAttributes[floydWarshall, HoldFirst];

(* computes transitive closure *)
(* "pass by reference": assigns to the symbol passed *)
floydWarshall[m_] := Module[
   {n = Length[m]},
   For[k = 1, k <= n, ++k,
     For[i = 1, i <= n, ++i,
      For[j = 1, j <= n, ++j,
       m[[i, j]] = m[[i, j]] || (m[[i, k]] && m[[k, j]]);
       ]
      ]
     ];
   ];

(* p 735 *)

letterCount[regex_] := Max@Cases[regex, letter[n_] :> n, Infinity];

regex2nfa[regex_] := regex2nfa[regex, letterCount[regex]];

regex2nfa[letter[n_], alphabetSize_] := {2, 
   alphabetSize, {ReplacePart[ConstantArray[{}, alphabetSize + 1], 
     n -> {2}], ConstantArray[{}, alphabetSize + 1]}, {2}, 1};

regex2nfa[or[first_, second_], alphabetSize_] :=
  nfaUnion[regex2nfa[first, alphabetSize], 
   regex2nfa[second, alphabetSize]];

regex2nfa[star[regex_], alphabetSize_] := 
  nfaStar[regex2nfa[regex, alphabetSize]];

regex2nfa[concat[first_, second_], alphabetSize_] := 
  nfaConcat[regex2nfa[first, alphabetSize], 
   regex2nfa[second, alphabetSize]];

(* closure properties: union, intersection, complement, \
concatenation, star, reverse *)

nfaUnion[{numStates1_Integer, alphabetSize1_Integer, 
    transitionMatrix1_, acceptStates1_?VectorQ, 
    initialState1_}, {numStates2_Integer, alphabetSize2_Integer, 
    transitionMatrix2_, acceptStates2_?VectorQ, 
    initialState2_}] := {numStates1 + numStates2 + 1, alphabetSize1,
   Join[
    {ReplacePart[ConstantArray[{}, alphabetSize1 + 1], 
      alphabetSize1 + 1 -> {initialState1 + 1, 
        initialState2 + 1 + numStates1}]}, transitionMatrix1 + 1, 
    transitionMatrix2 + 1 + numStates2], 
   Union[1 + acceptStates1, 1 + numStates1 + acceptStates2], 1};

(* make sure this isn't + *)
nfaStar[{numStates_Integer, alphabetSize_Integer, transitionMatrix_, 
    acceptStates_?VectorQ, initialState_}] := Module[
   {
    newT = transitionMatrix
    },
   Map[(newT[[#, alphabetSize + 1]] = 
       newT[[#, alphabetSize + 1]] \[Union] {initialState}) &, 
    acceptStates];
   {numStates, alphabetSize, newT, acceptStates, initialState}
   ];

nfaConcat[{numStates1_Integer, alphabetSize1_Integer, 
    transitionMatrix1_, acceptStates1_?VectorQ, 
    initialState1_}, {numStates2_Integer, alphabetSize2_Integer, 
    transitionMatrix2_, acceptStates2_?VectorQ, initialState2_}] := 
  Module[
   {
    newT1 = transitionMatrix1
    },
   Map[(newT1[[#, alphabetSize1 + 1]] = 
       newT1[[#, 
         alphabetSize1 + 1]] \[Union] {initialState2 + numStates1}) &,
     acceptStates1];
   {numStates1 + numStates2, alphabetSize1, 
    Join[newT1, transitionMatrix2 + numStates1], 
    acceptStates2 + numStates1, initialState1}
   ];

(* use on parsed regexes *)
regexReverse[letter[n_]] := letter[n];

regexReverse[or[args__]] := or @@ regexReverse /@ {args};

regexReverse[concat[args__]] := 
  concat @@ regexReverse /@ Reverse[{args}];

regexReverse[star[arg_]] := star[regexReverse[arg]];
End[] (* End Private Context *)

EndPackage[]
