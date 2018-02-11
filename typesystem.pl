% Will be handle later
% p(1).

p(X) :- X = 1.
p(X, Y) :- X = 1, Y = 1.
p(X, Y) :- X = 2, Y = 1.
% p(3,4). fails to check. ?? Should we support this?

mylen(L, Len) :- L = [], Len = 0.
mylen(L, Len) :- L = [_|T], mylen(T, TLen), Len is TLen + 1.

typeannot(X, int) :- integer(X).
typeannot(p, [int, int]).
typeannot(q, [int, int]).
typeannot(mylen, [list(tyvar(_A)), int]).

% tyvar predicate ensure that the definition is not more spezial
% than die type annotation
new_inst_tyvars(InTy, OutTy) :- 
   new_inst_tyvars_list([InTy], [OutTy]).
new_inst_tyvars_list(InTys, OutTys) :- 
   new_inst_tyvars_list_cxt(_, InTys, OutTys).

new_inst_tyvars_list_cxt(_Cxt, [], []).
new_inst_tyvars_list_cxt(Cxt, [In|InS], [Out|OutS]) :- 
   new_inst_tyvars_cxt(Cxt, In, Out), 
   new_inst_tyvars_list_cxt(Cxt, InS, OutS).

new_inst_tyvars_cxt(Cxt, tyvar(In), Out) :-
  tyvar_cxt_lookup(Cxt, tyvar(In), Out).
new_inst_tyvars_cxt(_Cxt, int, int).
new_inst_tyvars_cxt(_Cxt, unit, unit).
new_inst_tyvars_cxt(Cxt, list(In), list(Out)) :- 
   new_inst_tyvars_cxt(Cxt, In, Out).

tyvar_cxt_lookup(Context, tyvar(In), Out) :-
   var(Context), !, Out = _NewVar,
   Context = [(tyvar(In), Out)| _NewContext].
tyvar_cxt_lookup([(tyvar(In1), Out1)|_Cxt], tyvar(In2), Out2) :-
   In1 == In2, !, Out1 = Out2.
tyvar_cxt_lookup([(tyvar(In1), _)|Cxt], tyvar(In2), Out) :-
  In1 \== In2, !, context_write(Cxt, tyvar(In2), Out).

context_write(Context, Y, T) :-
  var(Context), !, Context = [(Y, T)| _NewContext].

context_write([(X, T1)|_Context], Y, T2) :-
  write("context_write check found"), nl,
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

hastype(Context, (A,B), unit) :-
  !,
  write("hastype conjunction"), nl,
  hastype(Context, A, unit), hastype(Context, B, unit).

hastype(Context, (A=B), unit) :-
  !,
  write("hastype equality"), nl,
  hastype(Context, A, T1), hastype(Context, B, T1).

hastype(Context, (A==B), unit) :-
  !,
  write("hastype structurall equivaltence"), nl,
  hastype(Context, A, T1), hastype(Context, B, T1).

hastype(Context, (A is B), unit) :-
  !,
  write("hastype 'is' builtin"), nl,
  hastype(Context, A, int), hastype(Context, B, int).

hastype(Context, (A + B), int) :-
  !,
  write("hastype '+' builtin"), nl,
  hastype(Context, A, int), hastype(Context, B, int).

hastype(_Context, A, Ty) :-
  A == [], !, Ty = list(_).
hastype(Context, A, Ty) :-
  A = [H|T], !, hastype(Context, H, Ty1),
  hastype(Context, T, Ty), Ty = list(Ty1).

hastype(Context, A, unit) :-
  A =.. [B|Params], atom(B), !,
  write("hastype predicate"), nl,
  typeannot(B, Ty),
  new_inst_tyvars_list(Ty, Ty2),
  checkparams(Context, Params, Ty2).


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
         hastype(Context, Body, _T)
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
