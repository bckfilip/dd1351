/*
working_directory(CWD, 'C:/Users/Jacob/Documents/Programmering/DD1351 Logik').
[labb2].

*/

verify(InputFileName) :- 
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof, Proof), !.

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

valid_proof(Prems, Goal, Proof, Proof) :-
    check_goal(Goal, Proof), 
    valid_proof(Prems, Proof, Proof).

valid_proof(_, _, []).

valid_proof(Prems, Proof, [ProofHead | ProofTail]) :-
    \+valid_row_seq(ProofHead, ProofTail), !, false;
    \+check_proof(Prems, Proof, ProofHead), !, false;
    valid_proof(Prems, Proof, ProofTail).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

valid_row_seq([_, _, _], []).

valid_row_seq([Row1 | Rest1], [Row2 | _Rest2]) :-
    /* check if first predicate after assumption is valid*/
    is_list(Row1),
    valid_row_seq(Row1, Rest1);

    is_list(Row2),
    valid_row_seq([Row1 | Rest1], Row2);
    
    ExpectedNextRow is Row1 + 1,
    ExpectedNextRow == Row2.

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
check_goal(Goal, Proof) :-
    last(Proof, [_RowNum, P, _]), 
    P == Goal.  

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* Elem is somewhere in the proof*/
in_proof(Elem, [ProofHead | ProofTail]) :-
    member(Elem, [ProofHead | ProofTail]);
    nth0(0, ProofHead, FirstElem), is_list(FirstElem), in_proof(Elem, ProofHead);
    in_proof(Elem, ProofTail).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/*Elem1 and Elem2 has to be on the same level */
same_level_in_proof(Elem1, Elem2, [ProofHead | ProofTail]) :-
    member(Elem1, [ProofHead | ProofTail]), member(Elem2, [ProofHead | ProofTail]);
    nth0(0, ProofHead, FirstElem), is_list(FirstElem), same_level_in_proof(Elem1, Elem2, ProofHead);
    same_level_in_proof(Elem1, Elem2, ProofTail).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* Elem1 and Elem2 is in an assumption 1 level higher than Caller.*/
elems_one_level_higher(Caller, Elem1, Elem2, [ProofHead | ProofTail]) :-
    member(Caller, [ProofHead | ProofTail]), 
    elems_one_level_higher_helper(Elem1, Elem2, [ProofHead | ProofTail]);
    nth0(0, ProofHead, FirstElem), is_list(FirstElem), elems_one_level_higher(Caller, Elem1, Elem2, ProofHead);
    elems_one_level_higher(Caller, Elem1, Elem2, ProofTail).

elems_one_level_higher_helper(Elem1, Elem2, [ProofHead | ProofTail]) :-
    nth0(0, ProofHead, FirstElem), is_list(FirstElem), member(Elem1, ProofHead), member(Elem2, ProofHead);
    elems_one_level_higher_helper(Elem1, Elem2, ProofTail).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/*
    We iterate through the proof until we reach a point where Goal is a member of the proof, aka we have reached a point where Goal is not in a nested list
    When this occurs, we try to find Elem in levels above or equal to the goal's level. 
    If goal is not a member of the proof, check if proofHead is a nestedList, if so call elem_can_see_fact on that nested list.
    If goal is not in the nested list or the ProofHead was not a nested list, then go to ProofTail.

    Ps. Goal is what is supposed to be seen as a fact
*/
caller_sees_fact(Fact, Caller, [ProofHead | ProofTail]) :-
    member(Fact, [ProofHead | ProofTail]),
    caller_sees_fact_helper(Caller, [ProofHead | ProofTail]);
    nth0(0, ProofHead, FirstElem), is_list(FirstElem), caller_sees_fact(Fact, Caller, ProofHead);
    caller_sees_fact(Fact, Caller, ProofTail).

/*
    We iterate through the proof until elem is a member of the proof. If this is the case we return true.
    If this is not the case we check if the proofHead is a nestedList, if so we call caller_sees_fact_helper on that nestedList.
    If the elem is not in the nestedList or the ProofHead was not a nested list, then go to ProofTail to check for other nestedLists
*/
caller_sees_fact_helper(Caller, [ProofHead | ProofTail]) :-
    member(Caller, [ProofHead | ProofTail]);

    nth0(0, ProofHead, FirstElem), is_list(FirstElem), 
    caller_sees_fact_helper(Caller, ProofHead);

    caller_sees_fact_helper(Caller, ProofTail).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* P måste tillhöra Prems*/
check_proof(Prems, _Proof, [_RowNum, P, premise]):-
    member(P, Prems).

check_proof(Prems, Proof, [[_RowNum, P, assumption] | Rest]) :-
    valid_proof([P | Prems], Proof, Rest).

/* P måste ses som ett fakta för att P ska kunna tas fram med copy(Ln) */
check_proof(_, Proof, [RowNum, P, copy(Ln)]) :-
    RowNum > Ln,
    caller_sees_fact([Ln, P, _], [RowNum, P, copy(Ln)], Proof).

/* Q och P måste ses som fakta för att and(P,Q) ska kunna tas fram med andint(Ln2,Ln1)*/
check_proof(_, Proof, [RowNum, and(P,Q), andint(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    caller_sees_fact([Ln1, Q, _], [RowNum, and(P,Q), andint(Ln2, Ln1)], Proof),
    caller_sees_fact([Ln2, P, _], [RowNum, and(P,Q), andint(Ln2, Ln1)], Proof).

/* and(P,_) måste ses som ett fakta för att P ska kunna tas fram med andel1(Ln)*/
check_proof(_, Proof, [RowNum, P, andel1(Ln)]) :-
    RowNum > Ln,
    caller_sees_fact([Ln, and(P,_), _], [RowNum, P, andel1(Ln)], Proof).

/* and(_, P) måste ses som ett fakta för att P ska kunna tas fram med andel2(Ln)*/
check_proof(_, Proof, [RowNum, P, andel2(Ln)]) :-
    RowNum > Ln,
    caller_sees_fact([Ln, and(_,P), _], [RowNum, P, andel2(Ln)], Proof).

/* or(P,_) måste ses som ett fakta för att P ska kunna tas fram med orint1(Ln)*/
check_proof(_, Proof, [RowNum, P, orint1(Ln)]) :-
    RowNum > Ln,
    caller_sees_fact([Ln, or(P,_), _], [RowNum, P, orint1(Ln)], Proof).

/* or(_, P) måste ses som ett fakta för att P ska kunna tas fram med orint2(Ln)*/
check_proof(_, Proof, [RowNum, P, orint2(Ln)]) :-
    RowNum > Ln,
    caller_sees_fact([Ln, or(_,P), _], [RowNum, P, orint2(Ln)], Proof).

/*
or(P,Q) måste ses som ett fakta från P och X perspektiv samt att P och X på samma nivå som varandra.
or(P,Q) måste ses som ett fakta från Q och X perspektiv samt att Q och X på samma nivå som varandra.
*/
check_proof(_, Proof, [RowNum, X, orel(Ln5, Ln4, Ln3, Ln2, Ln1)]) :-
    RowNum > Ln5, RowNum > Ln4, RowNum > Ln3, RowNum > Ln2, RowNum > Ln1,
    Ln5 < Ln4, Ln4 < Ln3, Ln3 < Ln2, Ln2 < Ln1,
    in_proof([Ln5, or(P,Q), _], Proof),

    caller_sees_fact([Ln5, or(P,Q), _], [Ln4, P, assumption], Proof),
    caller_sees_fact([Ln5, or(P,Q), _], [Ln3, X, _], Proof),
    same_level_in_proof([Ln4, P, assumption], [Ln3, X, _], Proof),
    
    caller_sees_fact([Ln5, or(P,Q), _], [Ln2, Q, assumption], Proof),
    caller_sees_fact([Ln5, or(P,Q), _], [Ln1, X, _], Proof),
    same_level_in_proof([Ln2, Q, assumption], [Ln1, X, _], Proof).

/* P och Q måste vara 1 nivå ovanför impint(Ln2,Ln1) för att imp(P,Q) ska kunna tas fram med imp(Ln2,Ln1) */
check_proof(_, Proof, [RowNum, imp(P,Q), impint(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    elems_one_level_higher([RowNum, imp(P,Q), impint(Ln2, Ln1)], [Ln1, Q, _], [Ln2, P, assumption], Proof).

/* imp(P,Q) och P måste ses som fakta för att Q ska kunna tas fram med impel */
check_proof(_, Proof, [RowNum, Q, impel(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    caller_sees_fact([Ln1, imp(P,Q), _], [RowNum, Q, impel(Ln2, Ln1)], Proof),
    caller_sees_fact([Ln2, P, _], [RowNum, Q, impel(Ln2, Ln1)], Proof).

/* cont och P måste vara 1 nivå ovanför negint(Ln2,Ln1) för att neg(P) ska kunna tas fram med negint(Ln2,Ln1) */
check_proof(_, Proof, [RowNum, neg(P), negint(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    elems_one_level_higher([RowNum, neg(P), negint(Ln2, Ln1)], [Ln1, cont, _], [Ln2, P, _], Proof).

/* neg(P) och P ska ses som fakta för att cont ska kunna tas fram med negel */
check_proof(_, Proof, [RowNum, cont, negel(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    caller_sees_fact([Ln1, neg(P), _], [RowNum, cont, negel(Ln2, Ln1)], Proof),
    caller_sees_fact([Ln2, P, _], [RowNum, cont, negel(Ln2, Ln1)], Proof).

/* This rule is just weird but apparently impossibility implies endless possibilites for some magical reason */
check_proof(_, Proof, [RowNum, _P, contel(Ln)]) :-
    RowNum > Ln,
    in_proof([Ln, cont, _], Proof).

/* P ska ses som fakta för att neg(neg(P)) ska kunna tas fram med negnegint */
check_proof(_, Proof, [RowNum, neg(neg(P)), negnegint(Ln)]) :-
    RowNum > Ln,   
    caller_sees_fact([Ln, P, _], [RowNum, neg(neg(P)), negnegint(Ln)], Proof).

/* neg(neg(P)) ska ses som fakta för att P ska kunna tas fram med negnegel */
check_proof(_, Proof, [RowNum, P, negnegel(Ln)]) :-
    RowNum > Ln,
    caller_sees_fact([Ln, neg(neg(P)), _], [RowNum, P, negnegel(Ln)], Proof).

/* neg(Q) och imp(P,Q) måste ses som fakta för att neg(P) ska kunna tas fram med mt */
check_proof(_, Proof, [RowNum, neg(P), mt(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    caller_sees_fact([Ln1, neg(Q), _], [RowNum, neg(P), mt(Ln2, Ln1)], Proof),
    caller_sees_fact([Ln2, imp(P,Q), _], [RowNum, neg(P), mt(Ln2, Ln1)], Proof).

/* cont och neg(P) måste vara 1 nivå ovanför pbc för att P ska kunna tas fram med pbc*/
check_proof(_, Proof, [RowNum, P, pbc(Ln2, Ln1)]) :-
    RowNum > Ln1, RowNum > Ln2,
    elems_one_level_higher([RowNum, P, pbc(Ln2, Ln1)], [Ln1, cont, _], [Ln2, neg(P), _], Proof).

/* Kan anropas varsom helst*/
check_proof(_, _, [_RowNum, or(P, neg(P)), lem]).
