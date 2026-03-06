% examples/summation.pl
% Summation from 1..N: sum(N, S) where S = 1+2+...+N

sum(0, 0).
sum(N, S) :-
    N > 0,
    N1 is N - 1,
    sum(N1, S1),
    S is S1 + N.
