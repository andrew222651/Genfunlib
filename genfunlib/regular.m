(* Mathematica Package *)

BeginPackage["genfunlib`regular`"]

(* protect global symbols used without any kind 
	of values *)
Protect[or, concat, star, EmptyWord];

(* TODO: usages for protected symbols *)

NFA::usage = "NFA[n, alphabet, transitions, acceptStates, initialState] is an NFA " ~~ 
				"with states [1..n], and transitions given by a matrix\n" ~~
			 "NFA[DFA[...]] is an NFA defined from a DFA\n" ~~
			 "NFA[Regex[...]] is an NFA defined from a symbolic regular expression\n" ~~
			 "NFA[RRGrammar[...]] is an NFA defined from a right regular grammar\n" ~~
			 "NFA[Digraph[...]] is an NFA defined from a digraph with labeled vertices";
DFA::usage = "DFA[n, alphabet, transitions, acceptStates, initialState] is an DFA " ~~ 
				"with states [1..n], and transitions given by a matrix\n" ~~
			 "DFA[NFA[...]] is a DFA defined from a NFA\n" ~~
			 "DFA[Regex[...]] is a DFA defined from a symbolic regular expression\n" ~~
			 "DFA[RRGrammar[...]] is a DFA defined from a right regular grammar\n" ~~
			 "DFA[Digraph[...]] is a DFA defined from a digraph with labeled vertices";
Regex::usage = "Regex is a wrapper for expressions built with Strings, or, concat, " ~~
				"star, and EmptyWord\n" ~~
			 "Regex[NFA[...]] is a symbolic regular expression defined from a NFA\n" ~~
			 "Regex[DFA[...]] is a symbolic regular expression defined from a DFA\n" ~~
			 "Regex[RegularExpression[\"regex\"]] is a symbolic regular expression " ~~
			    "defined from a restricted Mathematica regular expression\n" ~~
			 "Regex[RRGrammar[...]] is a symbolic regular expression defined " ~~
			 	"from a right regular grammar\n" ~~
			 "Regex[Digraph[...]] is a symbolic regular expression defined from a " ~~
		 		"digraph with labeled vertices";
RRGrammar::usage = "RRGrammar[{lhs -> rhs, ...}] is a right regular grammar given " ~~
				"by a list of productions\n" ~~
			 "RRGrammar[NFA[...]] is a right regular grammar defined from a NFA\n" ~~
			 "RRGrammar[DFA[...]] is a right regular grammar defined from a DFA\n" ~~
			 "DFA[Regex[...]] is a right regular grammar defined from a " ~~
			 	"symbolic regular expression\n" ~~
			 "RRGrammar[Digraph[...]] is a right regular grammar defined from a " ~~
		 		"digraph with labeled vertices";
Digraph::usage = "Digraph[graph, startVertices, endVertices, \[Epsilon]Accepted] " ~~
				"is a directed graph with labeled vertices for counting walks " ~~ 
				"from start vertices to end vertices\n" ~~
			 "Digraph[NFA[...]] is a directed graph defined from a NFA\n" ~~
			 "Digraph[DFA[...]] is a directed graph defined from a DFA\n" ~~
			 "Digraph[Regex[...]] is a directed graph defined from a " ~~
			 	"symbolic regular expression\n" ~~
			 "Digraph[RRGrammar[...]] is a directed graph defined " ~~
			 	"from a right regular grammar\n";				

Begin["`Private`"] (* Begin Private Context *) 


nonTerminals[RRGrammar[grammar_]] := (grammar /. Rule -> List)[[All, 1]];


NFA::invalid = "Invalid NFA.";
DFA::invalid = "Invalid DFA.";
RegularExpression::invalid = "Invalid Mathematica regular expression.";
Regex::invalid = "Invalid symbolic regular expression.";
RRGrammar::invalid = "Invalid right regular grammar.";
Digraph::invalid = "Invalid directed graph.";


validate[NFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
	initialState_]] := Module[
	{
		ok = True
	},
	ok = ok && Head[numStates] === Integer && numStates >= 0;
	ok = ok && MatchQ[alphabet, {__String}] && !MemberQ[alphabet, ""];
	ok = ok && (numStates == 0 || MatrixQ[transitionMatrix, MatchQ[#, {___Integer}] && 
		(Max[#] <= numStates && Min[#] >= 1) &]);
	ok = ok && (numStates == 0 || Dimensions[transitionMatrix, 2] == 
		{numStates, Length[alphabet] + 1});
	ok = ok && MatchQ[acceptStates, {___Integer}] && (numStates == 0 || 
		(Max[acceptStates] <= numStates && Min[acceptStates] >= 1));
	ok = ok && (numStates == 0 || (Head[initialState] === Integer && 
		1 <= initialState <= numStates));
	
	If[!ok, Message[NFA::invalid]];
	ok
];
validate[NFA[___]] := (Message[NFA::invalid];False);   

validate[DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
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
	
	If[!ok, Message[DFA::invalid]];
	ok
];
validate[DFA[___]] := (Message[DFA::invalid];False);   

validate[RegularExpression[regex_String]] := Module[
	{
		ok = True
	},
	ok = ok && StringMatchQ[regex, (LetterCharacter | DigitCharacter | "\\*" | "(" | 
    ")" | "|") ...];
    ok = ok && Check[StringMatchQ["", regex], $Failed] != $Failed;
    
    If[!ok, Message[RegularExpression::invalid]];
    ok
];
validate[RegularExpression[Null]] := True;
validate[RegularExpression[___]] := (Message[RegularExpression::invalid];False);

validateRawRegex[Null] := True;
validateRawRegex[EmptyWord] := True;
validateRawRegex[str_String /; str != ""] := True;
validateRawRegex[star[regex_]] := validateRawRegex[regex];
validateRawRegex[or[regexes__]] := And @@ validateRawRegex /@ {regexes};
validateRawRegex[concat[regexes__]] := And @@ validateRawRegex /@ {regexes};
validateRawRegex[___] := False;

validate[Regex[regex_]] := Module[
	{
		ok = True
	},
	ok = ok && validateRawRegex[regex];
	
	If[!ok, Message[Regex::invalid]];
	ok
];
validate[Regex[___]] := (Message[Regex::invalid];False);

validate[RRGrammar[grammar:{(_ -> _) ...}]] := Module[
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
	validateTerm[concat[str_String /; str != "", sym_Symbol[n_Integer] /; MemberQ[nonTerms, sym[n]]]] := True;
	validateTerm[_] := False;
	
	ok = ok && MatchQ[grammar[[All,2]], {( _?validateTerm | or[ _?validateTerm .. ]) ...}];
	
	If[!ok, Message[RRGrammar::invalid]];
	ok
];
validate[RRGrammar[___]] := (Message[RRGrammar::invalid];False);

validate[Digraph[graph_, startVertices_List, endVertices_List, True | False]] := Module[
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
	
	If[!ok, Message[Digraph::invalid]];
	ok
];
validate[Digraph[___]] := (Message[Digraph::invalid];False);


validationRule = HoldPattern[Optional[Pattern[val, 
	Rule[validationRequired, 
    	Alternatives[True,False]]],	Rule[validationRequired,True]]];


viaAlgorithms = {
   (* {to, from, via} *)
   {DFA, Regex, NFA},
   {DFA, RRGrammar, NFA},
   {DFA, Digraph, NFA},
   {Regex, NFA, DFA},
   {Regex, RRGrammar, DFA},
   {Regex, Digraph, DFA},
   {RRGrammar, DFA, NFA},
   {RRGrammar, Regex, NFA},
   {RRGrammar, Digraph, NFA},
   {Digraph, NFA, DFA},
   {Digraph, Regex, DFA},
   {Digraph, RRGrammar, DFA}
};

(* define conversion algorithms that go via 
	another conversion *)
(# /. {to_, from_, via_} :> 
      Hold[
      	to[name : from[___], validationRule] /; 
      	(! val[[2]] || validate[name]) := 
         to[via[name, validationRequired -> False]];]) & /@ 
  viaAlgorithms // ReleaseHold;


NFA[dfa: DFA[0, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], validationRule] /; 
    (!val[[2]] || validate[dfa]) :=
    NFA[0, alphabet, {}, {}, Null];

NFA[dfa: DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], validationRule] /; 
    If[!val[[2]] || validate[dfa], True, Message[NFA::invalidDFA]; False] := 
    NFA[numStates, alphabet, 
    	Transpose[Join[Transpose[Map[List, transitionMatrix, {2}]], 
    		ConstantArray[{}, numStates]]], 
    	acceptStates, initialState];

(* AC p 735 *)
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

NFA[RRGrammar[{}]] := NFA[0, {Null}, {}, {}, Null];

NFA[g: RRGrammar[grammar_], validationRule] /; 
    (!val[[2]] || validate[g]) :=
    Module[
    	{
    		(* added for rhs -> string rules *) acceptState = Unique[],
    		stateSet,
    		alphabet = Cases[grammar, _String, Infinity]//Union,
    		(* lookup functions *) stateNumber, alphabetNumber,
    		expandedGrammar,
    		transitionMatrix, acceptStates
    	},
    	If[alphabet == {}, Return[NFA[0, {Null}, {}, {}, Null]]];
    	
    	stateSet = Flatten[{Sort@nonTerminals[grammar], acceptState}];
    	
    	stateNumber[state_] := First@Flatten@Position[stateSet, 
    		state, {1}, Heads -> False];
    	alphabetNumber[str_] := First@Flatten@Position[alphabet, 
    		str, {1}, Heads -> False];
    	
    	acceptStates = {stateNumber[acceptState]};
    	
    	expandedGrammar = grammar /. (rhs_ -> or[args__]) :> 
    		Sequence@@((rhs -> # &) /@ {args});
    	transitionMatrix = ConstantArray[{}, {Length[stateSet], Length[alphabet] + 1}];
    	
    	Function[rule,
    		rule /. {
    					(lhs_ -> EmptyWord) :> (acceptStates = Union[acceptStates, {stateNumber[lhs]}];),
    					(lhs_ -> st:(_Symbol|_Symbol[n_])) :> (transitionMatrix[[stateNumber[lhs], -1]] = 
    						Union[transitionMatrix[[stateNumber[lhs], -1]], {stateNumber[st]}];),
    					(lhs_ -> concat[str_, st:(_Symbol|_Symbol[n_])])
    						:> (transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]] = 
    							Union[transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]], {stateNumber[st]}];),
    					(lhs_ -> str_String) 
    						:> (transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]] = 
    							Union[transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]], {stateNumber[acceptState]}];)
    			}
    	] /@ expandedGrammar;
    	
    	NFA[Length[stateSet], alphabet, transitionMatrix, acceptStates, grammar[[1,1]]//stateNumber]
];
    	
NFA[dg: Digraph[graph_, startVertices_, endVertices_, eAccepted_], 
	validationRule] /; 
    (!val[[2]] || validate[dg]) :=
    Module[
    	{
    		edges = EdgeList[graph], 
    		alphabet = 
    			Union[PropertyValue[{graph, #}, VertexLabels] & /@ 
      				VertexList[graph]], 
      		numStates, initialState, acceptState, 
   			transitionMatrix, vertex2LetterPos, edge2StatePos
   		}, 
  vertex2LetterPos[vertex_] := 
   First@Flatten@
     Position[alphabet, 
      PropertyValue[{graph, vertex}, VertexLabels], {1}, 
      Heads -> False];
  edge2StatePos[edge_] := 
   First@Flatten@Position[edges, edge, {1}, Heads -> False];
  {initialState, acceptState, numStates} = Length[edges] + {1, 2, 2};
  transitionMatrix = 
   ConstantArray[{}, {numStates, Length[alphabet] + 1}];
  If[eAccepted, 
   transitionMatrix[[initialState, 
      Length[alphabet] + 1]] = {acceptState}];
  Map[Function[vertex, 
    transitionMatrix[[initialState, vertex2LetterPos[vertex]]] = 
      Union[transitionMatrix[[initialState, 
         vertex2LetterPos[vertex]]], {acceptState}];], 
   Intersection[endVertices, startVertices]];
  Map[Function[edge, 
    transitionMatrix[[initialState, vertex2LetterPos[edge[[1]]]]] = 
      Union[
       transitionMatrix[[initialState, 
         vertex2LetterPos[edge[[1]]]]], {edge[[1]]}];], 
   Union@EdgeList[graph, 
     Alternatives @@ (DirectedEdge[#, _] & /@ startVertices)]];
  Map[Function[edge, 
    transitionMatrix[[edge2StatePos[edge], 
        vertex2LetterPos[edge[[2]]]]] = 
      Union[transitionMatrix[[edge2StatePos[edge], 
         vertex2LetterPos[edge[[2]]]]], {acceptState}];], 
   Union@EdgeList[graph, 
     Alternatives @@ (DirectedEdge[_, #] & /@ endVertices)]];
  Map[Function[edgePair, 
    transitionMatrix[[edge2StatePos[edgePair[[1]]], 
        vertex2LetterPos[edgePair[[1, 2]]]]] = 
      Union[transitionMatrix[[edge2StatePos[edgePair[[1]]], 
         vertex2LetterPos[edgePair[[1, 2]]]]], {edge2StatePos[
         edgePair[[2]]]}];], 
   Union@Flatten[
     Outer[List, EdgeList[graph, DirectedEdge[_, #]], 
        EdgeList[graph, DirectedEdge[#, _]]] & /@ VertexList[graph], 
     2]];
  NFA[numStates, alphabet, transitionMatrix, {acceptState}, 
   initialState]
];


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

makeTransitionMatrix[alphabetSize_, dfaStateSet_, transitionMatrix_, 
  ajacency_] := Table[
   Map[stateSubset \[Function]
     Position[dfaStateSet,
        Map[state \[Function]
            {transitionMatrix[[state, i]], 
             Map[Position[ajacency[[#]], True] &, 
              transitionMatrix[[state, i]]]}, stateSubset] // 
          Flatten // Union] // Flatten // First,
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

DFA[NFA[0, _, _, _, _]] := DFA[0, {Null}, {}, {}, Null];
    
DFA[nfa: NFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], validationRule] /; 
    (!val[[2]] || validate[nfa]) := Module[
   {
    dfaStateSet = Subsets[Range[numStates]],
    dfatransitionMatrix,
    dfaAcceptStates,
    dfaInitialState,
    (* ajacency matrix for states as vertices
    	and emoves as edges *)
    ajacency = Table[
      ReplacePart[ConstantArray[False, numStates], 
       List /@ (transitionMatrix[[k, -1]]) -> True],
      {k, 1, numStates}
      ],
     stateNumber
    },
   
   stateNumber[stateSet_] := Position[dfaStateSet, stateSet, {1}, Heads -> False]
   	//Flatten //First;
   
   floydWarshall[ajacency];
   (* ajacency is now transitive closure *)
   
   dfaInitialState = stateNumber[ 
       	{initialState, 
          Position[ajacency[[initialState]], True]} // Flatten // 
        Union];
   dfaAcceptStates = 
    Sort@Map[stateNumber, Select[
       dfaStateSet, (Intersection[#, acceptStates] != {}) &]];
   dfatransitionMatrix = 
    makeTransitionMatrix[Length[alphabet], dfaStateSet, transitionMatrix, 
     ajacency];
   {2^numStates, alphabet, dfatransitionMatrix, dfaAcceptStates, 
    dfaInitialState}//removeUnreachables//hopcroft
   ];

    	
simplifyRawRegex[regex_] := FixedPoint[
  Replace[#, {
     star[star[args__]] :> star[args],
     star[Null] -> EmptyWord,
     star[EmptyWord] -> EmptyWord,
     or[x_] :> x,
     or[i___, Null, f___] :> or[i, f],
     or[i___, x_, m___, x_, f___] :> or[i, x, m, f],
     or[i___, or[args__], f___] :> or[i, args, f],
     concat[i___, concat[args__], f___] :> concat[i, args, f],
     concat[x_] :> x,
     concat[___, Null, ___] -> Null,
     concat[i___, EmptyWord, f___] :> concat[i, f]
     }, {0, Infinity}] &,
  regex]

Regex[DFA[0, _, _, _, _]] := Regex[Null];

Regex[dfa: DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], validationRule] /; 
    (!val[[2]] || validate[dfa])  := 
  Module[{edgeRawRegex, k, i, j}, edgeRawRegex[_, _] = Null;
 MapIndexed[
  Function[{endState, pos},(*pos[[1]]=startState,pos[[2]]=letter*)
   edgeRawRegex[pos[[1]], endState] = 
     or[edgeRawRegex[pos[[1]], endState], alphabet[[pos[[2]]]]];], 
  transitionMatrix, {2}];
 (*setup beginning and end states*)
 edgeRawRegex[0, initialState] = EmptyWord;
 edgeRawRegex[x_?(MemberQ[acceptStates, #] &), numStates + 1] = 
  EmptyWord;
 For[k = 1, k <= numStates, ++k, 
  Do[edgeRawRegex[i, j] = 
     or[edgeRawRegex[i, j], 
       concat[edgeRawRegex[i, k], star[edgeRawRegex[k, k]], 
        edgeRawRegex[k, j]]] // simplifyRawRegex, {i, 
     Append[Range[k + 1, numStates + 1], 0]}, {j, 
     Append[Range[k + 1, numStates + 1], 0]}];];
 Regex[edgeRawRegex[0, numStates + 1]]
];


RRGrammar[NFA[0, _, _, _, _]] := {};

RRGrammar[nfa: NFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], validationRule] /; 
    (!val[[2]] || validate[nfa]) :=
    Module[
    	{
    		nonTermHead = Unique[],
    		nonTerms,
    		augmentedAlphabet = {alphabet, EmptyWord}//Flatten,
    		grammar,
    		posOfInitial
    	},
    	nonTerms = nonTermHead /@ Range[numStates];
    	grammar = Flatten@MapIndexed[
    		(* #1 == list of stateNums *)
    		(* #2[[1]] == stateNum, #2[[2]] == letterNum *)
    		(nonTermHead[#2[[1]]] -> or @@ (Function[st,
    			concat[augmentedAlphabet[[#2[[2]]]], st]] /@
    				#1)) &,
    		transitionMatrix,
    		{2}];
    	grammar = grammar /. concat[EmptyWord, x_] :> x;
    	grammar = grammar /. (_ -> or[]) :> Sequence[];
    	grammar = {grammar, (nonTermHead[#] -> EmptyWord) & /@ acceptStates}//Flatten;
    	
    	(* if the initial state has no outgoing edges, 
    		and is not an accepting state, return {} *) 
    	If[Position[grammar, nonTermHead[initialState]] == {}, Return[{}]];
    	(* if start state appears, make one of its rules the first one *)
    	posOfInitial = Position[grammar, nonTermHead[initialState]]//Flatten//First;
    	
    	grammar = Permute[grammar, Cycles[{{1, posOfInitial}}]];
    	
    	grammar
    ]; 

cartesian[lists__List] := Flatten[Outer[List, lists], Length[{lists}] - 1];

Digraph[dfa: DFA[0, _, _, _, _], validationRule] /; 
    (!val[[2]] || validate[dfa]) := Digraph[Graph[{}], {}, {}, False];
    
Digraph[dfa: DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], validationRule] /; 
    (!val[[2]] || validate[dfa]) := Module[
    	{
    		vertexSet = Flatten[MapIndexed[
    			(* #1 = to, #2[[1]] = from, #2[[2]] = letterNum *)
    			{#2[[1]], #1, #2[[2]]}&, transitionMatrix, {2}], 1],
    		vertexNum,
    		edgeSet,
    		graph,
    		startVertices, endVertices, eAccepted
    	},
    	(* ranking functon *)
    	vertexNum[vertex_] :=  Position[vertexSet, vertex, 
    		{1}, Heads -> False][[1, 1]];
    		
    	startVertices = vertexNum /@ Cases[vertexSet, {initialState, _, _}];
    	endVertices = vertexNum /@ Cases[vertexSet, {_, st_, _} /; 
    		MemberQ[acceptStates, st]];
    	eAccepted = MemberQ[acceptStates, initialState];
    	
    	(* create the edge set *)
    	edgeSet = Cases[cartesian[vertexSet, vertexSet],
    		{{_, c_, _}, {c_, _, _}}];
    	edgeSet = vertexNum /@ edgeSet;
    	edgeSet = edgeSet /. {i_, f_} :> DirectedEdge[i, f];
    	
    	graph = Graph[Range[Length[vertexSet]], edgeSet];
    	
    	(* add String labels to the vertices *)    	
    	(# /. {from_, to_, letterNum_} :> (PropertyValue[{graph, 
    		vertexNum[{from, to, letterNum}]}, VertexLabels] = 
    			alphabet[[letterNum]];))& /@ vertexSet;
    	
    	Digraph[graph, startVertices, endVertices, eAccepted]
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
