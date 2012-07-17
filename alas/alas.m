(* Mathematica Package *)

BeginPackage["alas`"]
(* Exported symbols added here with SymbolName::usage *)  

Begin["`Private`"] (* Begin Private Context *) 
(* TODO: more constructions, restrictions, additional parameters via \
additional atomic classes, attribute grammars, change sum and prod to \
+ and * *)

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

nonTerminals[spec_] := (spec /. Equal -> List)[[All, 1]];

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

Protect[labeled];

toGFeqns[spec_, indet_, labeled -> True] := 
     Module[{nonterminals = nonTerminals[
             spec]}, spec /. {eClass -> 1, 
             zClass :> indet, (sym_Symbol)?
                 (MemberQ[nonterminals, #1] & ) :> 
               sym[indet]} //. 
         {sum[first_, second_] :> 
             first + second, prod[first_, 
               second_] :> first*second, 
           seq[expr_] :> 1/(1 - expr), 
           cyc[expr_] :> Log[1/(1 - expr)], 
           set[expr_] :> Exp[expr]}]; 

toGFeqns[spec_, indet_, labeled -> False] := 
     Module[{nonterminals = nonTerminals[
             spec]}, spec /. {eClass -> 1, 
             zClass :> indet, (sym_Symbol)?
                 (MemberQ[nonterminals, #1] & ) :> 
               sym[indet]} //. 
         {sum[first_, second_] :> 
             first + second, prod[first_, 
               second_] :> first*second, 
           seq[expr_] :> 1/(1 - expr), 
           cyc[expr_] :> With[{k = Unique[]}, 
               Sum[(EulerPhi[k]/k)*
                   Log[1/(1 - expr /. indet -> 
                            indet^k)], {k, 1, Infinity}]], 
           multiset[expr_] :> 
             With[{k = Unique[]}, 
               Exp[Sum[(expr /. indet -> indet^k)/
                     k, {k, 1, Infinity}]]]}]; 
End[] (* End Private Context *)

EndPackage[]