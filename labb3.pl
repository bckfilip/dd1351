/*
working_directory(CWD, 'C:/Users/Jacob/Documents/Programmering/DD1351 Logik').
[labb3].
verify('fil namn').

eller

working_directory(CWD, 'C:/Users/Jacob/Documents/Programmering/DD1351 Logik').
[run_all_tests].
run_all_tests('labb3.pl').


% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% De riktade kanterna (om man representerar problemet som en graf)

% L - The labeling
% "nodegenskaper". De "värden" en specifik nod kan anta. t.ex s1 kan anta r,q 

% S - Current state
% Startnod

% U - Currently recorded states
% Besökta noder

% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S |- F
% U
% To execute: consult('your_file.pl'). verify('input.txt').
% Literals
%check(_, L, S, [], X) :- ...
%check(_, L, S, [], neg(X)) :- ...
% And
%check(T, L, S, [], and(F,G)) :- ...
% Or
% AX - In every node 1 level higher, Phi is satisfied.
% EX - In at least 1 node 1 level higher, Phi is satisfied.
% AG - In every node in all levels, Phi is satisfied.
% EG - In at least 1 node in some level, Phi is satisfied.
% AF - In all paths 1 level higher, Phi is satisfied somewhere.
% EF - In at least 1 path 1 level higher, Phi is satisfied somewhere.
*/

verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [S], F).

check(T, T, L, S, [S], F).

/*X is True eventuelly*/
check(T, [[Node | [AdjList]] | Rest], L, S, U, ex(X)) :-
    Node == S,
    performEX(AdjList, X, L, U);

    \+Node == S,
    check(Rest, L, S, U, ex(X)).  

/*X is True always*/
check(T, [[Node | [AdjList]] | Rest], L, S, U, ax(X)) :-
    Node == S,
    performAX(AdjList, X, L, U);

    \+Node == S,
    check(Rest, L, S, U, ax(X)).

/* EG */ 
check(T, [[Node | [AdjList]] | Rest], L, S, U, eg(X)) :-
    Node == S,
    /* check if startnode satisfies phi?*/ 
    \+satisfiesPhi(Node, L, X), !, false;
    Node == S,
    performEG(AdjList, T, L, S, U, eg(X));

    \+Node == S,
    check(Rest, T, L, S, U, eg(X)).

/* AG */
check(T, [[Node | [AdjList]] | Rest], L, S, U, ag(X)) :-
    Node == S,
    /* check if startnode satisfies phi?*/ 
    \+satisfiesPhi(Node, L, X), !, false;
    Node == S,
    performAG(AdjList, T, L, S, U, ag(X));

    \+Node == S,
    check(Rest, T, L, S, U, ag(X)).

/*  'Valid035.txt' or(p,neg(p)).*/ 
check(T, [[Node | [AdjList]] | Rest], L, S, U, or(X, Y)) :-
    check(T, [[Node | [AdjList]] | Rest], L, S, U, X);
    check(T, [[Node | [AdjList]] | Rest], L, S, U, Y).    


/* 'Valid087.txt' and(neg(q),neg(p)). */
check(T, [[Node | [AdjList]] | Rest], L, S, U, and(X, Y)) :-
    check(T, [[Node | [AdjList]] | Rest], L, S, U, X),
    check(T, [[Node | [AdjList]] | Rest], L, S, U, Y). 

/*Undersöker ifall X är sant utifrån antalet neg() */
negCounter(neg(_X), [], _).
negCounter(_X, [], _) :- false.

negCounter(X, [neg(Label), Rest], Num) :-
    NewNum is Num + 1,
    negCounter(X, [Label], NewNum);
    negCounter(X, [Rest], 0).

negCounter(X, [Label,  Rest], Num) :-
    member(X, [Label]),
    evenNum(Num);
    negCounter(X, [Rest], 0).

negCounter(X, [neg(Label)], Num) :- 
    NewNum is Num + 1,
    negCounter(X, [Label], NewNum).

negCounter(X, [Label], Num) :- 
    member(X, [Label]), 
    evenNum(Num).

evenNum(Num) :- 0 is mod(Num,2).

satisfiesPhi(CurrentNode, [[Node | [NodeLabels]] | Rest], X) :-   
    \+CurrentNode == Node,
    satisfiesPhi(CurrentNode, Rest, X);

    /*Checks if X is is true according to the NodeLabels*/
    negCounter(X, NodeLabels, 0).  

performEX([FirstN | Rest], Phi, L, U) :-
    /*if current node is new and satifies Phi */
    nodeNotUsed(FirstN, U), 
    satisfiesPhi(FirstN, L, Phi), !;
    /*if the current node is new but did not satisfy Phi, then we check the remaining nodes on the same level */
    nodeNotUsed(FirstN, U), 
    performEX(Rest, Phi, L, [U, FirstN]);
    /*if the current node is not new, then we check the remaining nodes on the same level */
    \+nodeNotUsed(FirstN, U), 
    performEX(Rest, Phi, L, U).

performAX([],_,_,_).

performAX([FirstN | Rest], Phi, L, U) :-
    /*if current node is new*/
    nodeNotUsed(FirstN, U), 
    satisfiesPhi(FirstN, L, Phi), 
    performAX(Rest, Phi, L, [U, FirstN]);
    /*if the current node is not new, then we check the remaining nodes on the same level */
    \+nodeNotUsed(FirstN, U), 
    performAX(Rest, Phi, L, U).

/* T, [[Node | [AdjList]] | Rest], L, S, U, eg(X)*/ 
performEG(_, [], _, _, _, _) :- false.
performEG(T, [FirstN | Rest], L, S, U, Phi) :- 
    /* if current node is new and satisfies phi we go deeper*/ 
    nodeNotUsed(FirstN, U),
    satisfiesPhi(FirstN, L, Phi),
    check(T, T, L, FirstN, [U, FirstN], Phi);

    /* New node but does not satisfy phi we check remaining nodes on same level*/ 
    nodeNotUsed(FirstN, U),
    \+satisfiesPhi(FirstN, L, Phi),
    performEG(T, Rest, L, S, [U, FirstN], Phi);

    /*if the current node is not new, then we check the remaining nodes on the same level */
    \+nodeNotUsed(FirstN, U), 
    performEG(T, Rest, L, S, U, Phi).

/* Håller i alla states, alla paths. 'Valid621.txt.'*/
performAG(_, [], _, _, _, _).
performAG(T, [FirstN | Rest], L, S, U, Phi) :- 
    nodeNotUsed(FirstN, U),
    satisfiesPhi(FirstN, L, Phi),
    check(T, T, L, FirstN, [U, FirstN], Phi),
    performAG(T, Rest, L, S, [U, FirstN], Phi);

    nodeNotUsed(FirstN, U),
    \+satisfiesPhi(FirstN, L, Phi), !, false;

    \+nodeNotUsed(FirstN, U),
    performAG(T, Rest, L, S, U, Phi).

nodeNotUsed(Elem, [Head | Tail]) :-
    \+member(Elem, [Head | Tail]);
    nth0(0, Head, First), is_list(First), nodeNotUsed(Elem, Head);
    nodeNotUsed(Elem, Tail).
     
    

