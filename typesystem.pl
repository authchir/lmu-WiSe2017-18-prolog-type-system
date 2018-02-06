% Will be handle later
% p(1).

p(X) :- X = 1.
p(X, Y) :- X = 1, Y = 1.
p(X, Y) :- X = 1, Y = 2.
p(X, Y) :- X = 1, Y = 3.

typeannot(X, int) :- integer(X).
typeannot(p, [int, int]).
typeannot(q, [int, int]).

context_write(Context, Y, T) :-
  var(Context), !, Context = [(Y, T)| _NewContext].

context_write([(X, T1)|_Context], Y, T2) :-
  write("context_write found"), nl,
  X == Y, !, T1 = T2.

context_write([(X, _)|Context], Y, T) :-
  X \== Y, context_write(Context, Y, T).

checkparams(_Context, [], []).
checkparams(Context, [X|Xs], [Ty|Tys]) :-
  hastype(Context, X, Ty),
  checkparams(Context, Xs, Tys).

hastype(Context, A, T) :-
  var(A), !,
  write("hastype variable"), nl,
  context_write(Context, A, T).

hastype(_Context, A, int) :-
  integer(A), !,
  write("hastype integer"), nl.

hastype(Context, (A,B), _T) :-
  !,
  write("hastype conjunction"), nl,
  hastype(Context, A, _T1), hastype(Context, B, _T2).

hastype(Context, (A=B), _T) :-
  !,
  write("hastype equality"), nl,
  hastype(Context, A, T1), hastype(Context, B, T1).

hastype(Context, A, Ty) :-
  A =.. [B|Params], atom(B), !,
  write("hastype predicate"), nl,
  checkparams(Context, Params, Ty).

zip([], [], _Zs).
zip([X|Xs], [Y|Ys], [Z|Zs]) :-
  Z = (X,Y),
  zip(Xs, Ys, Zs).

initcontext(Params, Tys, Context) :-
  zip(Params, Tys, Context).

checkrules :-
  forall(
    (typeannot(Id, Ty), atom(Id)),
    (length(Ty, TyLength),
      prettyprint(Id, Ty),
      functor(Head, Id, TyLength),
      forall(
        clause(Head, Body),
        (tab(2), write(Head), nl, tab(2), write(Body), nl,
         Head =.. [_|Params],
         initcontext(Params, Ty, Context),
         write(hastype(Context, Body, _T))
        )
      )
    )
  ).

prettyprint(Id, Ty) :-
  write(Id), tab(1), write(:), tab(1), write(Ty), nl.

samelength(XS, YS) :- length(XS, N), length(YS, N).

%?- current_predicate(p/X).
%X = 1 ;
%X = 2 ;
%false.
