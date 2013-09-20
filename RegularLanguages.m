(* Mathematica Package *)

BeginPackage["Genfunlib`RegularLanguages`"]

NFA::usage = "NFA[n, alphabet, transitions, acceptStates, initialState] is an NFA " <> 
                "with states [1..n], and transitions given by a matrix.";
DFA::usage = "DFA[n, alphabet, transitions, acceptStates, initialState] is an DFA " <> 
                "with states [1..n], and transitions given by a matrix.";
Regex::usage = "Regex is a wrapper for expressions built with strings, RegexOr, " <> 
                "RegexConcat, RegexStar, and EmptyWord.";
RRGrammar::usage = "RRGrammar[{lhs -> rhs, ...}] is a right regular grammar given " <>
                "by a list of productions.";
Digraph::usage = "Digraph[graph, startVertices, endVertices, \[Epsilon]Accepted] " <>
                "is a directed graph with labeled vertices for counting walks " <> 
                "from start vertices to end vertices.";
                
ToNFA::usage = "ToNFA[DFA[...]] is an NFA defined from a DFA.\n" <>
             "ToNFA[Regex[...]] is an NFA defined from a symbolic regular expression.\n" <>
             "ToNFA[RRGrammar[...]] is an NFA defined from a right regular grammar.\n" <>
             "ToNFA[Digraph[...]] is an NFA defined from a digraph with labeled vertices.";
ToDFA::usage = "ToDFA[NFA[...]] is a DFA defined from a NFA.\n" <>
             "ToDFA[Regex[...]] is a DFA defined from a symbolic regular expression.\n" <>
             "ToDFA[RRGrammar[...]] is a DFA defined from a right regular grammar.\n" <>
             "ToDFA[Digraph[...]] is a DFA defined from a digraph with labeled vertices.";
ToRegex::usage = "ToRegex[NFA[...]] is a symbolic regular expression defined from a NFA\n" <>
             "ToRegex[DFA[...]] is a symbolic regular expression defined from a DFA.\n" <>
             "ToRegex[RegularExpression[\"regex\"]] is a symbolic regular expression " <>
                "defined from a restricted Mathematica regular expression.\n" <>
             "ToRegex[RRGrammar[...]] is a symbolic regular expression defined " <>
                "from a right regular grammar.\n" <>
             "ToRegex[Digraph[...]] is a symbolic regular expression defined from a " <>
                "digraph with labeled vertices.";
ToRRGrammar::usage = "ToRRGrammar[NFA[...]] is a right regular grammar defined from a NFA.\n" <>
             "ToRRGrammar[DFA[...]] is a right regular grammar defined from a DFA.\n" <>
             "ToRRGrammar[Regex[...]] is a right regular grammar defined from a " <>
                "symbolic regular expression.\n" <>
             "ToRRGrammar[Digraph[...]] is a right regular grammar defined from a " <>
                "digraph with labeled vertices.";
ToDigraph::usage = "ToDigraph[NFA[...]] is a directed graph defined from a NFA.\n" <>
             "ToDigraph[DFA[...]] is a directed graph defined from a DFA.\n" <>
             "ToDigraph[Regex[...]] is a directed graph defined from a " <>
                "symbolic regular expression.\n" <>
             "ToDigraph[RRGrammar[...]] is a directed graph defined " <>
                "from a right regular grammar.";                

RegStar::usage = "RegStar[NFA[...]] performs the star operation on an NFA.\n" <>
             "RegStar[DFA[...]] performs the star operation on a DFA.\n" <>
             "RegStar[Regex[...]] performs the star operation on a symbolic regular expression.\n" <>
             "RegStar[RRGrammar[...]] performs the star operation on a right regular grammar.\n" <>
             "RegStar[Digraph[...]] performs the star operation on a directed graph.";

RegComplement::usage = "RegComplement[NFA[...], {\"str1\", \"str2\",...}] performs the " <> 
                "complement operation on an NFA with respect to a given alphabet.\n" <>
             "RegComplement[DFA[...], {\"str1\", \"str2\",...}] performs the complement " <>
                 "operation on a DFA with respect to a given alphabet.\n" <>
             "RegComplement[Regex[...], {\"str1\", \"str2\",...}] performs the " <>
                "complement operation on a symbolic regular expression with respect " <>
                "to a given alphabet.\n" <>
             "RegComplement[RRGrammar[...], {\"str1\", \"str2\",...}] performs the " <>
                "complement operation on a right regular grammar with respect to a given " <> 
                "alphabet.\n" <>
             "RegComplement[Digraph[...], {\"str1\", \"str2\",...}] performs the complement " <>
             "operation on a directed graph with respect to a given alphabet.";

RegReverse::usage = "RegReverse[NFA[...]] performs the reversal operation on an NFA.\n" <>
             "RegReverse[DFA[...]] performs the reversal operation on a DFA.\n" <>
             "RegReverse[Regex[...]] performs the reversal operation on a symbolic regular expression.\n" <>
             "RegReverse[RRGrammar[...]] performs the reversal operation on a right regular grammar.\n" <>
             "RegReverse[Digraph[...]] performs the reversal operation on a directed graph.";

RegUnion::usage = "RegUnion[NFA[...], NFA[...]] performs the reversal operation on two NFAs.\n" <>
             "RegUnion[DFA[...], DFA[...]] performs the reversal operation on two DFAs.\n" <>
             "RRegUnionRegex[...], Regex[...]] performs the reversal operation on two symbolic " <>
                "regular expressions.\n" <>
             "RegUnion[RRGrammar[...], RRGrammar[...]] performs the reversal operation on two " <>
                "right regular grammars.\n" <>
             "RegUnion[Digraph[...], Digraph[...]] performs the reversal operation on two directed " <>
                "graphs.";

RegConcat::usage = "RegConcat[NFA[...], NFA[...]] performs the concatenation operation on two NFAs.\n" <>
             "RegConcat[DFA[...], DFA[...]] performs the concatenation operation on two DFAs.\n" <>
             "ReRegConcategex[...], Regex[...]] performs the concatenation operation on two symbolic " <>
                "regular expressions.\n" <>
             "RegConcat[RRGrammar[...], RRGrammar[...]] performs the concatenation operation on two " <>
                "right regular grammars.\n" <>
             "RegConcat[Digraph[...], Digraph[...]] performs the concatenation operation on two directed " <>
                "graphs.";

RegIntersection::usage = "RegIntersection[NFA[...], NFA[...]] performs the intersection operation on two NFAs.\n" <>
             "RegIntersection[DFA[...], DFA[...]] performs the intersection operation on two DFAs.\n" <>
             "RegIntersection[Regex[...], Regex[...]] performs the intersection operation on two symbolic " <>
                "regular expressions.\n" <>
             "RegIntersection[RRGrammar[...], RRGrammar[...]] performs the intersection operation on two " <>
                "right regular grammars.\n" <>
             "RegIntersection[Digraph[...], Digraph[...]] performs the intersection operation on two directed " <>
                "graphs.";

ToRegularExpression::usage = "ToRegularExpression[Regex[...]] converts a symbolic regular " <>
            "expression to a Mathematica regular expression.";

RegexOr::usage = "RegexOr is a head used to define symbolic regular expressions.  It " <>
            "represents the regular expression equal to the union of its arguments."; 

RegexConcat::usage = "RegexConcat is a head used to define symbolic regular expressions.  It " <>
            "represents the regular expression equal to the concatentation of its arguments."; 

RegexStar::usage = "RegexStar is a head used to define symbolic regular expressions.  It " <>
            "represents the regular expression equal to the star of its argument."; 

RRGrammarOr::usage = "RRGrammarOr is a head used to define right regular grammars.  It " <>
            "represents a possible choice between its arguments.";

RRGrammarConcat::usage = "RRGrammarConcat is a head used to define right regular grammars.  It " <>
            "is used to concatenate a letter with a nonterminal symbol.";

EmptyWord::usage = "EmptyWord represents the empty word.  It may be used in symbolic regular expressions.";

GeneratingFunction::usage = "GeneratingFunction[Regex[...], {\"letter1\" -> expr1, \"letter2\" -> expr2,...}] " <>
            "gives the generating function for the regular language specified by a symbolic " <>
            "regular expression.  It takes as its second argument a list of rules giving a marker/weight " <>
            "for each letter in the alphabet.\n" <>
            GeneratingFunction::usage;

Begin["`Private`"] (* Begin Private Context *) 

publicSymbols = {NFA, DFA, Regex, RRGrammar, Digraph,
    ToNFA, ToDFA, ToRegex, ToRRGrammar, ToDigraph, ToRegularExpression,  
    RegStar, RegComplement, RegReverse, RegUnion, RegConcat, RegIntersection,
    Disambiguate, AmbiguousQ, 
    RegexOr, RegexConcat, RegexStar, EmptyWord,
    RRGrammarConcat, RRGrammarOr};

(* ::Section:: *)
(* Input validation *)

nonTerminals[RRGrammar[grammar_]] := Module[
    {
        extendedGrammar
    },
    (* expand or[...]'s into separate rules in extendedGrammar *)
    expandedGrammar = grammar /. (rhs_ -> RRGrammarOr[args__]) :> 
        Sequence@@((rhs -> # &) /@ {args});
    Union@Flatten[{
    grammar[[All, 1]],
    Cases[grammar, Verbatim[Rule][lhs_, sym_Symbol /; sym != EmptyWord
        ] -> {lhs, sym}],
    Cases[grammar, Verbatim[Rule][lhs_, sym_Symbol[n_]] -> {lhs, sym[n]}],
    Cases[grammar, Verbatim[Rule][lhs_, RRGrammarConcat[_, expr_]] -> expr]
    }]
]; 

NFA::invalid = "Invalid NFA.";
DFA::invalid = "Invalid DFA.";
RegularExpression::invalid = "Invalid Mathematica regular expression.";
Regex::invalid = "Invalid symbolic regular expression.";
RRGrammar::invalid = "Invalid right regular grammar.";
Digraph::invalid = "Invalid directed graph.";
GeneratingFunction::invalidRules = "Invalid rules.";
RegComplement::invalidAlphabet = "Invalid alphabet.";

validateRLR[NFA[numStates_Integer?NonNegative, alphabet:{___String}, 
    transitionMatrix_, acceptStates:{___Integer}, initialState:_Integer|Null]] :=
    Module[ {
    ok = True
    },
        (* alphabet is valid *)
        ok = ok && !MemberQ[alphabet, ""];
        
        (* matrix entries are valid lists *)
        ok = ok && ((numStates == 0 && transitionMatrix == {}) || 
            MatrixQ[transitionMatrix, MatchQ[#, {___Integer}] && 
            (Max[#] <= numStates && Min[#] >= 1) &]);
        
        (* matrix dimensions are correct *)
        ok = ok && ((numStates == 0 && transitionMatrix == {}) || 
            Dimensions[transitionMatrix, 2] == 
            {numStates, Length[alphabet] + 1});
        
        (* accept states are valid *)
        ok = ok && ((numStates == 0 && acceptStates == {}) || 
            (numStates > 0 && Max[acceptStates] <= numStates && Min[acceptStates] >= 1));
        
        (* initial state is valid *)
        ok = ok && ((numStates == 0 && initialState == Null) || 
            (numStates > 0 && 1 <= initialState <= numStates));
        
        If[ !ok, Message[NFA::invalid]];
        ok
    ];
validateRLR[NFA[___]] := (Message[NFA::invalid];False);   

validateRLR[DFA[numStates_Integer?NonNegative, alphabet:{___String}, 
    transitionMatrix_, acceptStates:{___Integer}, initialState:_Integer|Null]] :=
    Module[ {
    ok = True
    },
        (* alphabet is valid *)
        ok = ok && !MemberQ[alphabet, ""];
        
        (* matrix entries are valid numbers *)
        ok = ok && ((numStates == 0 && transitionMatrix == {}) || 
            MatrixQ[transitionMatrix, MatchQ[#, _Integer] && 
            (# <= numStates && # >= 1) &]);
        
        (* matrix dimensions are correct *)
        ok = ok && ((numStates == 0 && transitionMatrix == {}) || 
            Dimensions[transitionMatrix, 2] == 
            {numStates, Length[alphabet]});
        
        (* accept states are valid *)
        ok = ok && ((numStates == 0 && acceptStates == {}) || 
            (numStates > 0 && Max[acceptStates] <= numStates && Min[acceptStates] >= 1));
        
        (* initial state is valid *)
        ok = ok && ((numStates == 0 && initialState == Null) || 
            (numStates > 0 && 1 <= initialState <= numStates));
        
        If[ !ok, Message[DFA::invalid]];
        ok
    ];
validateRLR[DFA[___]] := (Message[DFA::invalid];False);   

validateRLR[RegularExpression[regex_String]] := Module[
    {
        ok = True
    },
    ok = ok && StringMatchQ[regex, (LetterCharacter | DigitCharacter | "\\*" | "(" | 
    ")" | "|") ...];
    (* test validity as a regex according to Mathematica *)
    ok = ok && Check[StringMatchQ["", RegularExpression[regex]], $Failed] =!= $Failed;
    
    If[!ok, Message[RegularExpression::invalid]];
    ok
];
validateRLR[RegularExpression[Null]] := True;
validateRLR[RegularExpression[___]] := (Message[RegularExpression::invalid];False);

validateRawRegex[Null] := True;
validateRawRegex[EmptyWord] := True;
validateRawRegex[str_String /; str != ""] := True;
validateRawRegex[RegexStar[regex_]] := validateRawRegex[regex];
validateRawRegex[RegexOr[regexes__]] := And @@ validateRawRegex /@ {regexes};
validateRawRegex[RegexConcat[regexes__]] := And @@ validateRawRegex /@ {regexes};
validateRawRegex[___] := False;

validateRLR[Regex[regex_]] := Module[
    {
        ok = True
    },
    ok = ok && validateRawRegex[regex];
    
    If[!ok, Message[Regex::invalid]];
    ok
];
validateRLR[Regex[___]] := (Message[Regex::invalid];False);

validateRLR[g:RRGrammar[grammar:{(_ -> _) ...}]] := Module[
    {
        ok = True,
        nonTerms = nonTerminals[g],
        validateTerm
    },
    (* validate left-hand sides *)
    ok = ok && MatchQ[nonTerms, {(_Symbol | _Symbol[_Integer]) ...}];
    
    (* validate right-hand sides *)
    validateTerm[EmptyWord] := True;
    validateTerm[sym_Symbol] := True;
    validateTerm[sym_Symbol[n_Integer]] := True;
    validateTerm[str_String /; str != ""] := True;
    validateTerm[RRGrammarConcat[str_String /; str != "", sym_Symbol]] := True;
    validateTerm[RRGrammarConcat[str_String /; str != "", sym_Symbol[n_Integer]]] := True;
    validateTerm[_] := False;
    
    ok = ok && MatchQ[grammar[[All,2]], {( _?validateTerm | RRGrammarOr[ _?validateTerm .. ]) ...}];
    
    If[!ok, Message[RRGrammar::invalid]];
    ok
];
validateRLR[RRGrammar[___]] := (Message[RRGrammar::invalid];False);

validateRLR[Digraph[graph_Graph, startVertices_List, endVertices_List, True | False]] := Module[
    {
        ok = True,
        vertices
    },
    (* validate graph *)
    ok = ok && (EmptyGraphQ[graph] || DirectedGraphQ[graph]);
    vertices = VertexList[graph];
    ok = ok && MatchQ[vertices, {___Integer}];
    
    (* make sure vertex labels are nonempty strings *)
    ok = ok && And @@ ( (Head[PropertyValue[{graph, #}, VertexLabels]] === String && 
        PropertyValue[{graph, #}, VertexLabels] != "") & /@ vertices );
    (* validate vertex lists *)
    ok = ok && Union[startVertices, endVertices, vertices] == Union[vertices];
    
    If[!ok, Message[Digraph::invalid]];
    ok
];
validateRLR[Digraph[___]] := (Message[Digraph::invalid];False);

validateRules[rules_, regex_] := Module[
    {
        strings = Cases[regex, _String, {0, Infinity}],
        ok = True
    },
    
    ok = ok && MatchQ[rules, {(_String -> _) ...}];
    
    ok = ok && Complement[strings, rules[[All, 1]]] == {};
    
    If[!ok, Message[GeneratingFunction::invalidRules]];
    ok
];

validateAlphabet[alphabet_] := Module[
    {
        ok = True
    },
    
    ok = ok && MatchQ[alphabet, {_String ...}];
    
    ok = ok && DeleteDuplicates[alphabet] == alphabet;
    
    If[!ok, Message[RegComplement::invalidAlphabet]];
    ok
];


(* ::Section:: *)
(* Regex2NFA *)

(* AC p 735 *)
regex2nfa[Null] := NFA[0, {}, {}, {}, Null];

regex2nfa[str_String] := NFA[
    2, 
    {str}, 
    {
        {{2}, {}},
        {{}, {}}
    }, 
    {2}, 1
];

regex2nfa[EmptyWord] := NFA[
    1, {},
    {
        {{}}
    },
    {1}, 1
];

regex2nfa[RegexOr[first_, rest__]] :=
  RegUnion[regex2nfa[first], regex2nfa[RegexOr[rest]]];

regex2nfa[RegexOr[regex_]] := regex2nfa[regex];

regex2nfa[RegexStar[regex_]] := 
  RegStar[regex2nfa[regex]];

regex2nfa[RegexConcat[first_, rest__]] := 
  RegConcat[regex2nfa[first], regex2nfa[RegexConcat[rest]]];

regex2nfa[RegexConcat[regex_]] := regex2nfa[regex];
   
ToNFA[Regex[regex_], OptionsPattern[]] := Module[
    {},
    (
    regex2nfa[regex]
    )/; !OptionValue[validationRequired] || validateRLR[Regex[regex]]
];

(* ::Section:: *)
(* RRGrammar2NFA *)

ToNFA[RRGrammar[{}], OptionsPattern[]] := NFA[0, {}, {}, {}, Null];

ToNFA[g: RRGrammar[grammar_], OptionsPattern[]] :=
    Module[
        {
            (* added for rhs -> string rules *) acceptState = Unique[],
            stateSet,
            alphabet = Cases[grammar, _String, Infinity]//Union,
            (* lookup functions *) stateNumber, alphabetNumber,
            expandedGrammar,
            transitionMatrix, acceptStates
        },
        (
        stateSet = Flatten[{nonTerminals[g], acceptState}];
        
        stateNumber[state_ /; MemberQ[stateSet, state]] := Position[stateSet, 
            state, {1}, Heads -> False][[1,1]];
        alphabetNumber[str_] := Position[alphabet, 
            str, {1}, Heads -> False][[1,1]];
        
        (* initialize acceptStates *)
        acceptStates = {stateNumber[acceptState]};
        
        (* expand or[...]'s into separate rules in extendedGrammar *)
        expandedGrammar = grammar /. (rhs_ -> RRGrammarOr[args__]) :> 
            Sequence@@((rhs -> # &) /@ {args});
        transitionMatrix = ConstantArray[{}, {Length[stateSet], Length[alphabet] + 1}];
        
        (* incorporate each rule into transitionMatrix and acceptStates *)
        Function[rule,
            rule /. {
            (lhs_ -> EmptyWord) :> (acceptStates = Union[acceptStates, {stateNumber[lhs]}];),
                (lhs_ -> st:(_Symbol|_Symbol[_])) :> (transitionMatrix[[stateNumber[lhs], -1]] = 
                    Union[transitionMatrix[[stateNumber[lhs], -1]], {stateNumber[st]}];),
                (lhs_ -> RRGrammarConcat[str_, st:(_Symbol|_Symbol[_])])
                    :> (transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]] = 
                        Union[transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]], {stateNumber[st]}];),
                (lhs_ -> str_String) 
                    :> (transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]] = 
                        Union[transitionMatrix[[stateNumber[lhs], alphabetNumber[str]]], {stateNumber[acceptState]}];)
            }
        ] /@ expandedGrammar;
        
        NFA[Length[stateSet], alphabet, transitionMatrix, acceptStates, grammar[[1,1]]//stateNumber]
        
        ) /; (!OptionValue[validationRequired] || validateRLR[g])
];

(* ::Section:: *)
(* Digraph2NFA *)
        
ToNFA[dg: Digraph[graph_, startVertices_, endVertices_, eAccepted_], 
    OptionsPattern[]] :=
    Module[
        {
            edges = EdgeList[graph], 
            alphabet = 
                Union[PropertyValue[{graph, #}, VertexLabels] & /@ 
                    VertexList[graph]], 
            numStates, initialState, acceptState, 
            transitionMatrix, vertex2LetterPos, edge2StatePos
        }, 
  (
  (* the states are all edges, plus a start state and an accept state *)
  
  (* lookup alphabet number for vertex *)
  vertex2LetterPos[vertex_] := 
   Position[alphabet, 
      PropertyValue[{graph, vertex}, VertexLabels], {1}, 
      Heads -> False][[1,1]];
  (* lookup state number for edge *)
  edge2StatePos[edge_] := 
   Position[edges, edge, {1}, Heads -> False][[1,1]];
   
  {initialState, acceptState, numStates} = Length[edges] + {1, 2, 2};
  
  (* initialize transitionMatrix *)
  transitionMatrix = 
   ConstantArray[{}, {numStates, Length[alphabet] + 1}];
   
  (* add emove from initial state to accept state if eAccepted *)
  If[eAccepted, 
   transitionMatrix[[initialState, -1]] = {acceptState}];
  
  (* if a vertex is a start vertex and an end vertex, add an
    edge labeled with its label from initialState to acceptState *)  
  Map[Function[vertex, 
    transitionMatrix[[initialState, vertex2LetterPos[vertex]]] = 
      Union[transitionMatrix[[initialState, 
         vertex2LetterPos[vertex]]], {acceptState}];], 
   Intersection[endVertices, startVertices]];
  
  (* if an edge begins at a start vertex, add an edge labeled with
    that start vertex's label between initialState and the state
    corresponding to the edge in the digraph *) 
  Map[Function[edge, 
    transitionMatrix[[initialState, vertex2LetterPos[edge[[1]]]]] = 
      Union[
       transitionMatrix[[initialState, 
         vertex2LetterPos[edge[[1]]]]], {edge2StatePos[edge]}];], 
   EdgeList[graph, DirectedEdge[Alternatives@@startVertices, _]] 
  ];
  
  (* if an edge ends at an end state, add a transition from that edge
    to acceptState labeled by the end state's label *)
  Map[Function[edge, 
    transitionMatrix[[edge2StatePos[edge], 
        vertex2LetterPos[edge[[2]]]]] = 
      Union[transitionMatrix[[edge2StatePos[edge], 
         vertex2LetterPos[edge[[2]]]]], {acceptState}];], 
   EdgeList[graph, DirectedEdge[_, Alternatives@@endVertices]]
  ];
  
  (* if one edge goes into a vertex and one edge comes out,
    add a transition between the edges labeled with the label
    of the common vertex *)
  Map[Function[edgePair, 
    transitionMatrix[[edge2StatePos[edgePair[[1]]], 
        vertex2LetterPos[edgePair[[1, 2]]]]] = 
      Union[transitionMatrix[[edge2StatePos[edgePair[[1]]], 
         vertex2LetterPos[edgePair[[1, 2]]]]], {edge2StatePos[
         edgePair[[2]]]}];], 
   Union@Flatten[
     Outer[List, EdgeList[graph, DirectedEdge[_, #]], 
        EdgeList[graph, DirectedEdge[#, _]]] & /@ VertexList[graph], 
     2]
  ];
  
  NFA[numStates, alphabet, transitionMatrix, {acceptState}, 
   initialState]
   )/; !OptionValue[validationRequired] || validateRLR[dg]
];

(* ::Section:: *)
(* NFA2DFA *)

(* http://en.wikipedia.org/wiki/DFA_minimization#Hopcroft \
.27s_algorithm *)
hopcroft[DFA[numStates:(0|1), alphabet_, transitionMatrix_, acceptStates_, 
    initialState_]] := 
  DFA[numStates, alphabet, transitionMatrix, acceptStates, initialState];

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

SetAttributes[floydWarshall, HoldFirst];
(* computes transitive closure *)
(* "pass by reference": assigns to the symbol passed *)
floydWarshall[m_] := Module[
   {n = Length[m],i,j,k},
   For[k = 1, k <= n, ++k,
     For[i = 1, i <= n, ++i,
      For[j = 1, j <= n, ++j,
       m[[i, j]] = m[[i, j]] || (m[[i, k]] && m[[k, j]]);
       ]
      ]
     ];
];

(* states with no path to an accept state *)
deadStates[NFA[numStates_, _, transitionMatrix_, acceptStates_, _]] :=
   Module[
   {adj = Flatten /@ transitionMatrix}, 
   graph = Graph[
     Range[numStates],
     MapIndexed[DirectedEdge[First[#2], #1] &, adj, {2}] // Flatten];
   Complement[Range[numStates], 
    VertexInComponent[graph, acceptStates]
   ]
];

ToDFA[nfa:NFA[0, alphabet_, _, _, _], OptionsPattern[]] := Module[
    {},
    (
    DFA[0, alphabet, {}, {}, Null]
    ) /; !OptionValue[validationRequired] || validateRLR[nfa]
];
    
ToDFA[nfa : 
    NFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
     initialState_], OptionsPattern[]] := Module[
   {
    states = {}, queue, 
    adjacency = 
     Table[ReplacePart[ConstantArray[False, numStates], 
       List /@ (transitionMatrix[[k, -1]]) -> True], {k, 1, 
       numStates}],
    nfaDeadStates = deadStates[nfa],
    tr, state, neighbor,
    dfaInitialState, dfaAcceptStates, stateNumber, 
    dfaTransitionMatrix
    },
   (
     If[MemberQ[nfaDeadStates, initialState], 
      Return[DFA[0, {}, {}, {}, Null]]];
     floydWarshall[adjacency];
     queue = {Complement[
        Flatten[{initialState, 
          Position[adjacency[[initialState]], True]}], nfaDeadStates]};
     While[Length[queue] > 0,
      {state, queue} = {First[queue], Rest[queue]};
      If[! MemberQ[states, state],
       For[i = 1, i <= Length[alphabet], ++i,
        neighbor = 
         Flatten[Map[
            Function[
             st, {transitionMatrix[[st, i]], 
              Map[Position[adjacency[[#]], True] &, 
               transitionMatrix[[st, i]]]}], state
            ]]~Complement~nfaDeadStates;
        tr[state, i] = neighbor;
        queue = Append[queue, neighbor];
        ];
       states = Append[states, state];
       ];
      ];
     tr[_, _] = {};
     stateNumber[set_] := 
      Position[states, set, {1}, Heads -> False][[1, 1]];
     dfaAcceptStates = 
      stateNumber /@ 
       Select[states, (Intersection[#, acceptStates] != {}) &];
     dfaTransitionMatrix = 
      Table[stateNumber@tr[states[[s]], a], {s, 1, Length[states]}, {a, 1, 
        Length[alphabet]}];
     DFA[Length[states], alphabet, dfaTransitionMatrix, 
       dfaAcceptStates, 1] // hopcroft
     ) /; ! OptionValue[validationRequired] || validateRLR[nfa]
];
   
(* ::Section:: *)
(* DFA2Regex *)
        
simplifyRawRegex[regex_] := FixedPoint[
  Replace[#, {
     RegexStar[RegexStar[args__]] :> RegexStar[args],
     RegexStar[Null] -> EmptyWord,
     RegexStar[EmptyWord] -> EmptyWord,
     RegexOr[x_] :> x,
     RegexOr[i___, Null, f___] :> RegexOr[i, f],
     RegexOr[i___, x_, m___, x_, f___] :> RegexOr[i, x, m, f],
     RegexOr[i___, RegexOr[args__], f___] :> RegexOr[i, args, f],
     RegexConcat[i___, RegexConcat[args__], f___] :> RegexConcat[i, args, f],
     RegexConcat[x_] :> x,
     RegexConcat[___, Null, ___] -> Null,
     RegexConcat[i___, EmptyWord, f___] :> RegexConcat[i, f]
     }, {0, Infinity}] &,
  regex]

ToRegex[DFA[0, _, _, _, _], OptionsPattern[]] := Regex[Null];

ToRegex[dfa: DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], OptionsPattern[]] := 
  Module[
    {edgeRawRegex, k, i, j}, 
    (
    edgeRawRegex[_, _] = Null;
 MapIndexed[
  Function[{endState, pos},
   (*pos[[1]]=startState, pos[[2]]=letter*)
   edgeRawRegex[pos[[1]], endState] = 
     RegexOr[edgeRawRegex[pos[[1]], endState], alphabet[[pos[[2]]]]];], 
  transitionMatrix, {2}];
 (*setup beginning and end states*)
 edgeRawRegex[0, initialState] = EmptyWord;
 edgeRawRegex[x_?(MemberQ[acceptStates, #] &), numStates + 1] = 
  EmptyWord;
 For[k = 1, k <= numStates, ++k, 
  Do[edgeRawRegex[i, j] = 
     RegexOr[edgeRawRegex[i, j], 
       RegexConcat[edgeRawRegex[i, k], RegexStar[edgeRawRegex[k, k]], 
        edgeRawRegex[k, j]]] // simplifyRawRegex, {i, 
     Append[Range[k + 1, numStates + 1], 0]}, {j, 
     Append[Range[k + 1, numStates + 1], 0]}
  ];
 ];
 Regex[edgeRawRegex[0, numStates + 1]]
 )/; !OptionValue[validationRequired] || validateRLR[dfa]
];

(* ::Section:: *)
(* NFA2RRGrammar *)

ToRRGrammar[NFA[0, _, _, _, _], OptionsPattern[]] := RRGrammar[{}];

ToRRGrammar[nfa: NFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], OptionsPattern[]]  :=
    Module[
        {
            nonTermHead = Unique[],
            nonTerms,
            augmentedAlphabet = {alphabet, EmptyWord}//Flatten,
            grammar,
            posOfInitial
        },
        (
        nonTerms = nonTermHead /@ Range[numStates];
        grammar = Flatten@MapIndexed[
            (* #1 == list of stateNums *)
            (* #2[[1]] == stateNum, #2[[2]] == letterNum *)
            (nonTermHead[#2[[1]]] -> RRGrammarOr @@ (Function[st,
                RRGrammarConcat[augmentedAlphabet[[#2[[2]]]], nonTermHead[st]]] /@
                    #1)) &,
            transitionMatrix, {2}
        ];
        grammar = grammar /. RRGrammarConcat[EmptyWord, x_] :> x;
        grammar = grammar /. (_ -> RRGrammarOr[]) :> Sequence[];
        grammar = grammar /. (lhs_ -> RRGrammarOr[arg_]) :> (lhs -> arg);
        (* handle acceptStates *)
        grammar = {grammar, (nonTermHead[#] -> EmptyWord) & /@ acceptStates}//Flatten;
        
        (* if the initial state has no outgoing edges, 
            and is not an accepting state, return {} *) 
        If[FreeQ[grammar[[All, 1]], nonTermHead[initialState]], Return[RRGrammar[{}]]];
        (* if start state appears, make one of its rules the first one *)
        posOfInitial = Position[grammar, nonTermHead[initialState]][[1, 1]];
        
        If[posOfInitial != 1,
            grammar = Permute[grammar, Cycles[{{1, posOfInitial}}]]
        ];
        
        RRGrammar[grammar]
        )/; !OptionValue[validationRequired] || validateRLR[nfa]
    ]; 

(* ::Section:: *)
(* DFA2Digraph *)

cartesian[lists___List] := Flatten[Outer[List, lists, 1], Length[{lists}] - 1];

ToDigraph[DFA[0, _, _, _, _], OptionsPattern[]] := Digraph[Graph[{}], {}, {}, False];
    
ToDigraph[dfa: DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], OptionsPattern[]] := Module[
        {
            (* each transition corresponds to a vertex *)
            vertexSet = Flatten[MapIndexed[
                (* #1 = to, #2[[1]] = from, #2[[2]] = letterNum *)
                {#2[[1]], #1, #2[[2]]}&, transitionMatrix, {2}], 1],
            vertexNum,
            edgeSet,
            graph,
            startVertices, endVertices, eAccepted
        },
        (
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
        edgeSet = Map[vertexNum, edgeSet, {2}];
        edgeSet = edgeSet /. {i_, f_} :> DirectedEdge[i, f];
        
        graph = Graph[Range[Length[vertexSet]], edgeSet];
        
        (* start vertices are colored green, end vertices have dotted edges *)
        (PropertyValue[{graph, #}, VertexStyle] = Green;)& /@ startVertices;
        (PropertyValue[{graph, #}, VertexStyle] = EdgeForm[{Thick, Dotted}];)& /@ endVertices;
        (PropertyValue[{graph, #}, VertexStyle] = 
            Directive[Green, EdgeForm[{Thick, Dotted}]];)& /@ Intersection[startVertices, endVertices];
        
        (* add String labels to the vertices *)     
        (# /. {from_, to_, letterNum_} :> (PropertyValue[{graph, 
            vertexNum[{from, to, letterNum}]}, VertexLabels] = 
                alphabet[[letterNum]];))& /@ vertexSet;
        
        Digraph[graph, startVertices, endVertices, eAccepted]
        )/; !OptionValue[validationRequired] || validateRLR[dfa]
];

(* ::Section:: *)
(* Regular expression conversions *)

(* crappy: "," not allowed in the regex *)
pars[""] := EmptyWord;
pars[regex_] := 
  Module[{temp=regex},
    (*insert commas between things that are concatenated*)
   temp = FixedPoint[
     StringReplace[#, 
       a_ ~~ b_ /; 
         a != "(" && b != ")" && b != "*" && a != "," && b != "," && 
          a != "|" && b != "|" :> a <> "," <> b] &, temp];
   (*insert EmptyWord*)
   temp = FixedPoint[
     StringReplace[#, 
        {
            "||" -> "|EmptyWord|", 
            "(|" -> "(EmptyWord|", 
            "|)" -> "|EmptyWord)", 
            "()" -> "(EmptyWord)"
        }] &, temp];
   temp = StringReplace[temp, "*" -> "^2"];
   temp = StringReplace[temp, "," -> "**"];
   temp = ToExpression[temp, InputForm, Hold];
   temp = 
    Replace[temp, 
     sym_Symbol?( 
          !MemberQ[{Hold, RegexOr, RegexConcat, RegexStar, 
            EmptyWord}, #] &) :> 
      Module[{chars = Characters@ToString[Unevaluated[sym]]},
       If[Length[chars] == 1, chars[[1]],
        RegexConcat @@ chars
        ]
       ], Infinity];
   temp = 
    FixedPoint[
     Replace[#, {Power[expr_, _] :> RegexStar[expr], 
        NonCommutativeMultiply[args__] :> RegexConcat[args], 
        Verbatim[Alternatives][args__] :> RegexOr[args]}, {0, 
        Infinity}] &, temp];
   ReleaseHold[temp]
];

ToRegex[RegularExpression[Null], OptionsPattern[]] := Regex[Null];

ToRegex[r:RegularExpression[regex_], OptionsPattern[]] := Module[
    {},
    Regex@pars["(" <> regex <> ")"] /; !OptionValue[validationRequired] || validateRLR[r]
]; 

regex2regularexpression[Null] := Null;
regex2regularexpression[str_String] := str;
regex2regularexpression[EmptyWord] := "()";
regex2regularexpression[RegexStar[expr_]] := "(" <> regex2regularexpression[expr] <> ")*";
regex2regularexpression[RegexConcat[args__]] := StringJoin[regex2regularexpression /@ {args}];
regex2regularexpression[RegexOr[args__]] := "(" <> 
    StringJoin[Riffle[regex2regularexpression /@ {args},"|"]] <> ")";

ToRegularExpression[r:Regex[regex_], OptionsPattern[]] := Module[
    {simp = simplifyRawRegex[regex]},
    RegularExpression[regex2regularexpression[simp]] /; 
        !OptionValue[validationRequired] || validateRLR[r]
];


(* ::Section:: *)
(* Closure properties *)

RegStar[RRGrammar[{}], OptionsPattern[]] := RRGrammar[{Unique[] -> EmptyWord}];

RegStar[grammar : RRGrammar[_], OptionsPattern[]] := Module[
    {
        initial1 = grammar[[1, 1, 1]]
    },
    (
    RRGrammar[Flatten[{ initial1 -> EmptyWord,
    Replace[First[grammar],
        {
            Verbatim[Rule][nonTerm_, EmptyWord] :> (nonTerm -> 
                RRGrammarOr[initial1, EmptyWord]),
            RRGrammarOr[pre___, EmptyWord, post___] :> 
                RRGrammarOr[pre, EmptyWord, initial1, post]
        },
        Infinity
    ]}]]
    )/; !OptionValue[validationRequired] || validateRLR[grammar]
];

RegComplement[dfa:DFA[numStates_, alphabet_, transitionMatrix_, acceptStates_, 
    initialState_], compAlphabet_, OptionsPattern[]] := Module[
    {
        compDFA, intersectionAlphabet = Intersection[alphabet, compAlphabet],
        intersectionAlphabetRegex, 
        compNotAlphabetLetters = Complement[compAlphabet, alphabet],
        compNotAlphabetRegex
    },
    (
    compDFA = If[numStates == 0,
        (* no states *)
        If[alphabet == {},
            ToDFA[Regex[EmptyWord]],
            ToDFA[Regex[RegexStar[RegexOr@@alphabet]]]
        ],
        (* states *)
        DFA[numStates, alphabet, transitionMatrix, 
        Complement[Range[numStates], acceptStates], initialState]
    ];

    (* union(compDFA \[Intersection] intersectionAlphabet*, 
        words in compAlphabet* but not in alphabet* *)
    
    intersectionAlphabetRegex = If[intersectionAlphabet == {},
        Regex[EmptyWord],
        Regex[RegexStar[RegexOr@@intersectionAlphabet]]
    ];
    
    compNotAlphabetRegex = If[compNotAlphabetLetters == {},
        Regex[Null],
        Regex[RegexConcat[
            RegexStar[RegexOr@@compAlphabet],
            RegexOr@@compNotAlphabetLetters,
            RegexStar[RegexOr@@compAlphabet]]
        ]
    ];
        
    RegUnion[RegIntersection[ToRegex[compDFA], intersectionAlphabetRegex], 
        compNotAlphabetRegex]//ToDFA
    )/; !OptionValue[validationRequired] || 
        (validateRLR[dfa] && validateAlphabet[compAlphabet]) 
];


regexReverse[str_String] := str;

regexReverse[Null] := Null;

regexReverse[RegexOr[args__]] := RegexOr @@ regexReverse /@ {args};

regexReverse[EmptyWord] := EmptyWord;

regexReverse[RegexConcat[args__]] := 
  RegexConcat @@ regexReverse /@ Reverse[{args}];

regexReverse[RegexStar[arg_]] := RegexStar[regexReverse[arg]];

RegReverse[Regex[regex_], OptionsPattern[]] := Module[
    {},
    (
    Regex[regexReverse[regex]]
    )/; !OptionValue[validationRequired] || validateRLR[Regex[regex]]
];

RegUnion[grammar1 : RRGrammar[_], RRGrammar[{}], OptionsPattern[]] := Module[
    {},
    (
    grammar1
    )/; !OptionValue[validationRequired] || validateRLR[grammar1]
];
RegUnion[RRGrammar[{}], grammar2 : RRGrammar[_], OptionsPattern[]] := Module[
    {},
    (
    grammar2
    )/; !OptionValue[validationRequired] || validateRLR[grammar2]
];

RegUnion[grammar1 : RRGrammar[_], grammar2 : RRGrammar[_], OptionsPattern[]] :=
Module[
    {
        nonTerms1 = nonTerminals[grammar1],
        nonTerms2 = nonTerminals[grammar2],
        initial1, initial2,
        commonNonTerms,
        replacements, rules
    },
    (
    commonNonTerms = Intersection[nonTerms1, nonTerms2];
    replacements = Table[Unique[], {Length[commonNonTerms]}];
    rules = MapThread[Rule, {commonNonTerms, replacements}];
    initial1 = grammar1[[1, 1, 1]]; 
    initial2 = grammar2[[1, 1, 1]] /. rules;

    RRGrammar[{Unique[] -> RRGrammarOr[initial1, initial2],
        grammar1//First, grammar2 /. rules //First}//Flatten]

    )/; !OptionValue[validationRequired] || 
    (validateRLR[grammar1] && validateRLR[grammar2])
];

RegConcat[grammar1 : RRGrammar[_], RRGrammar[{}], OptionsPattern[]] := Module[
    {},
    RRGrammar[{}] /; !OptionValue[validationRequired] || 
        validateRLR[grammar1]
];

RegConcat[grammar1 : RRGrammar[_], grammar2 : RRGrammar[_], OptionsPattern[]] :=
Module[
    {
        nonTerms1 = nonTerminals[grammar1],
        nonTerms2 = nonTerminals[grammar2],
        initial2,
        commonNonTerms,
        replacements, rules
    },
    (
        commonNonTerms = Intersection[nonTerms1, nonTerms2];
        replacements = Table[Unique[], {Length[commonNonTerms]}];
        rules = MapThread[Rule, {commonNonTerms, replacements}];
        initial2 = grammar2[[1, 1, 1]] /. rules;

        RRGrammar[Flatten[{
            First[grammar1] /. {
                Verbatim[Rule][nonTerm_, EmptyWord] :> 
                    (nonTerm -> initial2),
                RRGrammarOr[pre___, EmptyWord, post___] :>
                    RRGrammarOr[pre, initial2, post]
            }, First[grammar2] /. rules
        }]]
    )/; !OptionValue[validationRequired] || 
    (validateRLR[grammar1] && validateRLR[grammar2])
];

RegIntersection[dfa1:DFA[numStates1_, alphabet1_, transitionMatrix1_, acceptStates1_, 
    initialState1_], dfa2:DFA[numStates2_, alphabet2_, transitionMatrix2_, 
    acceptStates2_, initialState2_], OptionsPattern[]] := Module[
    {
        newAlphabet = Intersection[alphabet1, alphabet2],
        stateSet = cartesian[Range[numStates1], Range[numStates2]],
        stateNum,
        newTransitionMatrix, newAcceptStates, newInitialState,
        alphabet1Num, alphabet2Num
    },
    (
    If[numStates1 == 0 || numStates2 == 0, 
        Return[DFA[0, newAlphabet, {}, {}, Null]];
    ];
    
    alphabet1Num[alphabetNum_] := Position[alphabet1, newAlphabet[[alphabetNum]], 
        {1}, Heads -> False][[1, 1]];
    alphabet2Num[alphabetNum_] := Position[alphabet2, newAlphabet[[alphabetNum]], 
        {1}, Heads -> False][[1, 1]];
    
    stateNum[state_] := Position[stateSet, state, {1}, Heads-> False][[1, 1]];
    
    newInitialState = stateNum[{initialState1, initialState2}];
    
    newAcceptStates = stateNum /@ Select[stateSet, 
        MemberQ[acceptStates1, #[[1]]] && MemberQ[acceptStates2, #[[2]]]&];
    
    newTransitionMatrix = Table[
        stateNum[
            {
                transitionMatrix1[[stateSet[[state]][[1]], alphabet1Num[c]]],
                transitionMatrix2[[stateSet[[state]][[2]], alphabet2Num[c]]]
            }
        ],
        {state, 1, Length[stateSet]},
        {c, 1, Length[newAlphabet]}
    ];
        
    DFA[Length[stateSet], newAlphabet, newTransitionMatrix, 
        newAcceptStates, newInitialState]
    )/; !OptionValue[validationRequired] || 
        (validateRLR[dfa1] && validateRLR[dfa2])
];

(* ::Section:: *)
(* To generating functions *)

(* takes an unambiguous regex *)
regex2GF[regex_, rules_] := 
FixedPoint[Replace[#,
    {
        str_String :> (str /. rules),
        Null -> 0,
        EmptyWord -> 1,
        RegexOr[args__] :> Plus[args],
        RegexConcat[args__] :> Times[args],
        RegexStar[arg_] :> 1/(1 - arg)
    },
    {0, Infinity}]&,
    regex
];


previousOptions = Options[GeneratingFunction]

Unprotect[GeneratingFunction];
Options[GeneratingFunction] = Union[
    previousOptions,
    {validationRequired -> True}
];
Protect[GeneratingFunction];

Unprotect[GeneratingFunction];
GeneratingFunction[regex:Regex[_], rules_, OptionsPattern[]] := 
    Module[
        {},
        (
        regex2GF[First@ToRegex@ToDFA@regex, rules]
        )/; !OptionValue[validationRequired] || validateRules[rules, regex]
    ];
Protect[GeneratingFunction];

(* ::Section:: *)
(* Code generation for repetitive bits and pieces *)

viaAlgorithms = {
   (* {to, from, via} *)
   {ToNFA, DFA, ToRegex},
   {ToDFA, Regex, ToNFA},
   {ToDFA, RRGrammar, ToNFA},
   {ToDFA, Digraph, ToNFA},
   {ToRegex, NFA, ToDFA},
   {ToRegex, RRGrammar, ToDFA},
   {ToRegex, Digraph, ToDFA},
   {ToRRGrammar, DFA, ToNFA},
   {ToRRGrammar, Regex, ToNFA},
   {ToRRGrammar, Digraph, ToNFA},
   {ToDigraph, NFA, ToDFA},
   {ToDigraph, Regex, ToDFA},
   {ToDigraph, RRGrammar, ToDFA}
};

(* define conversion algorithms that go via 
    another conversion *)
(# /. {to_, from_, via_} :> 
      Hold[
        to[name : from[___], opts:OptionsPattern[]]  := 
         to[via[name, opts], validationRequired -> False];
      ]) & /@ 
  viaAlgorithms // ReleaseHold;

(* complement *)
complementVias = {NFA, Regex, RRGrammar, Digraph};

(Hold[
        RegComplement[name : #[___], alpha_, opts:OptionsPattern[]]  := 
         ToExpression["To" <> ToString[#]][
            RegComplement[ToDFA[name, opts], alpha, validationRequired -> False]
         ];
      ]) & /@ 
  complementVias // ReleaseHold;

(* star and reverse *)
starReverseVias = {
    {RegStar, DFA, ToRRGrammar},
    {RegStar, Regex, ToRRGrammar},
    {RegStar, NFA, ToRRGrammar},
    {RegStar, Digraph, ToRRGrammar},
    {RegReverse, NFA, ToRegex},
    {RegReverse, DFA, ToRegex},
    {RegReverse, RRGrammar, ToRegex},
    {RegReverse, Digraph, ToRegex}
};

(# /. {op_, rlr_, via_} :> Hold[
        op[name : rlr[___], opts:OptionsPattern[]]  := 
         ToExpression["To" <> ToString[rlr]][
            op[via[name, opts], validationRequired -> False]
         ];
      ]) & /@ 
  starReverseVias // ReleaseHold;

(* union, concat, intersection *)
uciVias = {
    {RegUnion, DFA, ToRRGrammar},
    {RegUnion, Regex, ToRRGrammar},
    {RegUnion, NFA, ToRRGrammar},
    {RegUnion, Digraph,  ToRRGrammar},
    {RegConcat, DFA, ToRRGrammar},
    {RegConcat, Regex, ToRRGrammar},
    {RegConcat, NFA, ToRRGrammar},
    {RegConcat, Digraph, ToRRGrammar},
    {RegIntersection, NFA, ToDFA},
    {RegIntersection, Regex, ToDFA},
    {RegIntersection, RRGrammar, ToDFA},
    {RegIntersection, Digraph,  ToDFA}
};

(# /. {op_, rlr_, via_} :> Hold[
        op[name1 : rlr[___], name2 : rlr[___], opts:OptionsPattern[]]  := 
         ToExpression["To" <> ToString[rlr]][
            op[via[name1, opts], via[name2, opts], validationRequired -> False]
         ];
      ]) & /@ 
  uciVias // ReleaseHold;
         

(* add options for downvalued symbols except GeneratingFunction *)
(* also the symbols with catch-all definitions *)
symbolsWithOptions = {
    ToNFA, ToDFA, ToRegex, ToRRGrammar, ToDigraph, ToRegularExpression,  
    RegStar, RegComplement, RegReverse, RegUnion, RegConcat, RegIntersection
};

(MessageName[#, "invalidArgumentSyntax"] = "Invalid argument syntax.")& /@ 
    symbolsWithOptions;

Hold[#[___] /; (Message[#::invalidArgumentSyntax]; False) := Null;]& /@ 
    symbolsWithOptions //ReleaseHold;

(Options[#] = {validationRequired -> True})& /@ symbolsWithOptions;

End[] (* End Private Context *)
             
EndPackage[]
