:- multifile(typeannot/2).

typeannot(factorial, [int, int]).
factorial(0, 1) :- !.
factorial(N, M) :-
  N2 is N - 1,
  factorial(N2, N3),
  M is N3 * N.

typeannot(factorial_tail, [int, int, int]).
factorial_tail(0, ACC, ACC) :- !.
factorial_tail(N, ACC, M) :-
  N2 is N - 1,
  ACC2 is ACC * N,
  factorial_tail(N2, ACC2, M).

typeannot(factorial_test, []).
factorial_test :-
  N0 = 0, M0 = 1,   factorial(N0, M0), factorial_tail(N0, 1, M0),
  N1 = 1, M1 = 1,   factorial(N1, M1), factorial_tail(N1, 1, M1),
  N2 = 2, M2 = 2,   factorial(N2, M2), factorial_tail(N2, 1, M2),
  N3 = 3, M3 = 6,   factorial(N3, M3), factorial_tail(N3, 1, M3),
  N4 = 4, M4 = 24,  factorial(N4, M4), factorial_tail(N4, 1, M4),
  N5 = 5, M5 = 120, factorial(N5, M5), factorial_tail(N5, 1, M5),
  N6 = 6, M6 = 720, factorial(N6, M6), factorial_tail(N6, 1, M6).
