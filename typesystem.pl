% Will be handle later
% p(1).

p(X) :- X = 1.
p(X, Y) :- X = 1, Y = 1.

hastype(X, int) :- integer(X).
hastype(p, [int]).

typecheck :-
  forall(
    (hastype(Id, Ty), nonvar(Id)),
    (length(Ty, TyLength),
    functor(H, Id, TyLength),
    forall(
      clause(H, _B),
      (H =.. [ Id | Arg ],
      )))).



samelength(XS, YS) :- length(XS, N), length(YS, N).
zip(_XS, _YS, _XYS) :- true.
