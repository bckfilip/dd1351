/*
working_directory(CWD, 'C:/Users/Jacob/Documents/Programmering/DD1351 Logik').
[labb3B].
verify('labb3B.pl'). 
*/

:- discontiguous(check/5).

verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
/* 
    EX: 
    Get the adjcency list for S and check if any of them satisfies X, this is done via backtracking the choice of Node when check fails. */
check(T, L, S, _U, ex(X)) :-
    member([S, AdjList], T),
    member(Node, AdjList),
    check(T, L, Node, [], X).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
/* 
    AX: 
    Get the adjcency list for S and if it's longer than 0, then we check if each node satisfies X. 
    We send [] as U since we want each level in the call to have it's own U list to avoid loops in all levels in the call. */
check(T, L, S, _U, ax(X)) :-
    member([S, AdjList], T),
    \+length(AdjList, 0),
    performAX(T,L,AdjList, [], X).

performAX(T, L, [Node | Rest], U, X) :-
    check(T, L, Node, U, X),
    performAX(T, L, Rest, U, X).

performAX(_T,_L,[],_U,_X).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
/* 
    EF: 
    Check if X is true in S, if so then X is true in all futures.
    Otherwise, we check if X is true for one of the startNodes children.
    This is done via backtracking the choice of Node when check fails. Since we stay in the ef call, we must add S to U continously to know which nodes this call has visited. */
check(T, L, S, U, ef(X)) :-
    nodeNotUsed(S, U),
    (
        check(T, L, S, [], X);

        member([S, AdjList], T), member(Node, AdjList),
        check(T, L, Node, [S | U], ef(X))
    ).    

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
/* 
    AF: 
    Check if X is true in S, if so then X is true in all futures. 
    Otherwise, we check if X is true for all of the startNodes children. Since we stay in the same af call, we must add S to U contously to know which nodes this call has visited. */
check(T, L, S, U, af(X)) :-
    nodeNotUsed(S, U),
    (
        check(T, L, S, [], X);
    
        member([S, AdjList], T), \+length(AdjList, 0),
        performAF(T, L, AdjList, [S | U], X)
    ).

/* We check if Node passes check, which only happens if it's unvisited and contains X, if so then we move onto the next node. */
performAF(T, L, [Node | Rest], U, X) :-
    check(T, L, Node, U, af(X)),
    performAF(T, L, Rest, U, X).

/* All the children satisfied X so we return True.  
wait
af(and(verified, schedule))

and(ax(verified), ef(schedule)).
*/
performAF(_T,_L,[],_U,_X).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
/* 
    EG: 
    Check if X is true in S and all nodes in one of its childrens paths. A child's path ends when it reaches a node already visited or when there are no more children left. */ 
check(T, L, S, U, eg(X)) :-
    nodeNotUsed(S, U),
    check(T, L, S, [], X),
    member([S, AdjList], T),
    (
        member(Node, AdjList), check(T, L, Node, [S | U], eg(X)); 
        
        length(AdjList,0)
    );

    \+nodeNotUsed(S, U).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* 
    AG:
    We check if X is true in S and all nodes in one of its childrens paths. A child's path ends when it reaches a node already visited. */
check(T, L, S, U, ag(X)) :-
    nodeNotUsed(S, U),
    check(T, L, S, [], X),
    member([S, AdjList], T),
    (
        length(AdjList,0);

        performAG(T, L, AdjList, [S | U], X)
    );

    \+nodeNotUsed(S, U).

/* We check if each child in AdjList satisfies X. */
performAG(T, L, [Node | Rest], U, X) :-
    check(T, L, Node, U, ag(X)),
    performAG(T, L, Rest, U, X).

/* All the children satisfied X.*/
performAG(_T, _L, [], _U, _X).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* 
    OR:
    We return true if either X or Y is true from the startNode. We have empty lists since we want each call to begin with an empty list. */
check(T, L, S, [], or(X, Y)) :-
    check(T, L, S, [], X);
    check(T, L, S, [], Y);
    !, false.

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/*  
    AND:
    We return true if either X and Y is true from the startNode. We have empty lists since we want each call to begin with an empty list. */
check(T, L, S, [], and(X,Y)) :-
    check(T, L, S, [], X),
    check(T, L, S, [], Y);
    !, false.

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* 
    Variables:
    We check if X is in the nodeLabels for S, which is only the case when X is a variable (p, q, r, and such). */
check(_T, L, S, _U, X) :-
    member([S, NodeLabels], L),
    member(X, NodeLabels).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/*
    Negation:
    We check if X is NOT true from the startNode, if so then neg(X) must be true. */
check(T, L, S, _U, neg(X)) :-
    \+ check(T, L, S, [], X).

/*-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* Small helper functions with clearer names*/
nodeNotUsed(Elem, List) :-
    \+member(Elem, List).