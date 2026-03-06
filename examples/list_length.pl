% examples/list_length.pl
% List length: my_length(L, N) where N = |L|

my_length([], 0).
my_length([_|T], N) :-
    my_length(T, N1),
    N is N1 + 1.
