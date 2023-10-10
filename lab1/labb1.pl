/*
working_directory(CWD, 'C:/Users/Jacob/Documents/Programmering/DD1351 Logik').
[labb1].
*/

/* T=f(a,Y,Z), T=f(X,X,b).
T = f(a, a, b),
Y = X, X = a,
Z = b.

*/

/*--------------------------------------------------------------------------------------------------------------------------------------*/

/*
Tests:
remove_duplicates([],[],L).
remove_duplicates([1,2,3,2,1,2,5],[],L).
*/

/* If the given list is empty, return empty */
remove_duplicates([], _, []).

/* If the head is in our accumulator, the head is not unique so we move on. 
   We have ! (cut) because we use backtracking, so it will present solutions where member is false even tho that will give us an incorrect answer
   Therefore, we stop the backtracking after the first success.
*/
remove_duplicates([Head | Tail], Acc, UniqueList) :-
    member(Head, Acc), !,
    remove_duplicates(Tail, Acc, UniqueList).

/* If the head is not in our accumulator, we add it to our accumulator and Unique list 
   We want the order in UniqueList to be unchanged, therefore we build it recursively, 
   while we just input the head into acc since the order there doesn't matter.
*/
remove_duplicates([Head | Tail], Acc, [Head | UniqueList]) :-
    remove_duplicates(Tail, [Head | Acc], UniqueList).

/* It's a function since the predicate returns a list, not a boolean.*/

/*--------------------------------------------------------------------------------------------------------------------------------------*/

/*
Tests:
partstring([],L,F).
partstring([1],L,F).
partstring([1,2,3],L,F).
partstring([1,2,3,4,5,6,7],L,F).
*/

/*
If length of list is 0 then the input is invalid. 
*/
partstring(List,L,F) :-
    \+length(List, 0),
    length(F,L),
    L > 0,
    length(List, ListLength),
    (ListLength = L, genererate_lists(List,L,F), !; 
    genererate_lists(List,L,F)).

/*If ListLength > L then we can find letter sequences. */
genererate_lists([Head|Tail],L,F) :-
    partstring_helper([Head|Tail],L,F);
    genererate_lists(Tail,L,F).

partstring_helper(_, 0, []).

/*This is used to find out a sequence of length L given a list since it adds an element to F in each iteration and returns when L = 0.
When the list no longer has a tail but L is > 0 then it will return false. */
partstring_helper([Head | Tail], L, [Head | F]) :-
    L > 0,  
    NewL is L - 1,
    partstring_helper(Tail, NewL, F).


/*---------------------------------------------------------------------------------------------------------------------------------------- */

/*
Tests:
traverse(1,3,P).
traverse(1,1,P).

*/

edge(1,2).
edge(2,3).
edge(3,1).
edge(2,4).
edge(4,5).
edge(5,3).
                 
connected(X,Y) :- edge(X,Y) ; edge(Y,X).

/*Swap places with A and B to get right output*/
traverse(A,B,P) :-
    A \== B,
    traverse(B,A,[B],P).
/*If they are connected then we have found a valid path so we add B to the nodes in the path. */
traverse(A,B,Visited, [B|Visited]) :-
    connected(A,B).
/*Otherwise, we try to find another path to B using a different node that we have not visited yet*/
traverse(A,B,Visited,P) :-
    connected(A,X),
    X \== B,
    \+member(X,Visited),
    traverse(X,B,[X|Visited],P).

