% examples/reverse.pl
% Reverse with accumulator: rev(L, Acc, R) or my_reverse(L, R)

rev([], Acc, Acc).
rev([H|T], Acc, R) :-
    rev(T, [H|Acc], R).

my_reverse(L, R) :-
    rev(L, [], R).
