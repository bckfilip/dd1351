% For sicstus: use_module(library(lists)).  before consulting the file.

run_all_tests(ProgramToTest) :-
    catch(consult(ProgramToTest),
          B,
          (write('Could not consult \"'), write(ProgramToTest),
           write('\": '), write(B), nl, halt)),
    all_valid_ok(['valid005.txt', 'valid014.txt', 'test1.txt',
                  'test2.txt', 'test3.txt', 'test4.txt']),
    write('All tests passed.').

/* 
'invalid08.txt',
*/

all_valid_ok([]).
all_valid_ok([Test | Remaining]) :-
    write(Test), 
    (verify(Test), write(' passed');
    write(' failed. The proof is valid but your program rejected it!')),
    nl, all_valid_ok(Remaining).

all_invalid_ok([]).
all_invalid_ok([Test | Remaining]) :-
    write(Test), 
    (\+verify(Test), write(' passed');
    write(' failed. The proof is invalid but your program accepted it!')),
    nl, all_invalid_ok(Remaining).
