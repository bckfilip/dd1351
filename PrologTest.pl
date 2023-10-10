/* 
To create commens, use procent sign for single line.
Anyway, to change current working directory, aka CWD, type (working_directory(CWD, 'C:/Users/Jacob/Documents/Programmering/DD1351 Logik')). Obs kom ihåg att ändra alla rikningen på alla slashes
this is the knowledgebase. To compile it, in swi-prolog type [file name will all lowercase]. All the queries will take place in swi-prolog

:- kan läsas som "om", dvs implikation fast åt vänster "<-". Exempel: A är sann OM B och C är sann - A :- B, C 
"," mellan operatorer är "och", dvs "^".
";" mellan operatorer är "eller".

member(X,L) :- select(X,L,_).

remove_duplicates([],[]).

last_elem([E], E).
last_elem([_|T], E) 
    :- last_elem(T,E)

listLength([], 0).
listLength([E], 1).
listLength([H|T], Length) :-
    listLength(T,NewLength),
    L is NewLength + 1. 

node: 1        2        3     
     [0, 1, 2, 0, 1, 3, 0, 2]

startnode = 3
counter = 3 - 1 = 2

startnode = 2
counter = 2 - 1 = 1

startnode = 1
counter = 1 - 1 = 0


find_start_node([Head | Tail], 0, EndNode, Path) :-
    Head > 0, 
    Head = EndNode,
    find_start_node(Tail, StartNode, EndNode, Path).

find_start_node([Head | Tail], StartNode, EndNode, Path) :-
    Head > 0,
    find_start_node(Tail, StartNode, EndNode, Path).

find_start_node([Head | Tail], StartNode, EndNode, Path) :-
    Head = 0,
    Counter is StartNode - 1,
    find_start_node(Tail, Counter, EndNode, Path).

edge(1,2).
edge(1,3).
edge(2,3).
edge(3,4).
edge(4,6).
edge(5,3).
edge(5,1).
edge(6,5).

path(A, B, Path) :-
    travel(A,B,[A],Q).

travel(A,B,P,[B|P]) :-
    connected(A,B).

travel(A,B,Visited,Path) :-
    edge(A,C),
    C \== B, 
    \+member(C,Visited),
    travel(C,B,[C|Visited],Path).

compare_edges_to_end()

connected(X,Y) :- edge(X,Y) ; edge(Y,X).

path(A,B,Path) :-
       travel(A,B,[A],Q).

Check if A and B is connected, either way we add B to the current path. 
travel(A,B,P,[B|P]) :- 
       connected(A,B).
travel(A,B,Visited,Path) :-
       connected(A,C),           
       C \== B,
       \+member(C,Visited),
       travel(C,B,[C|Visited],Path). 

*/ 


weather(islamabad, summer, hot).
weather(karachi, summer, warm).
weather(islamabad, winter, cold).


/* If the given list is empty, return empty */
remove_duplicates([], Acc, []).

/* If the head is in our accumulator, the head is not unique so we move on. */
remove_duplicates([Head | Tail], Acc, UniqueList) :-
    member(Head, Acc),  
    remove_duplicates(Tail, Acc, UniqueList).

/* If the head is not in our accumulator, we add it to our accumulator and Unique list */
remove_duplicates([Head | Tail], Acc, [Head | UniqueList]) :-
    remove_duplicates(Tail, [Head | Acc], UniqueList).