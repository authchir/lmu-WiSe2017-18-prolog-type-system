:- multifile(typeannot/2).
:- multifile(decltype/3).
:- dynamic(is_checking/5).
:- dynamic(checking_preds/2).

system_type(unit).
system_type(int).
system_type(tyvar(_)).
system_type(list(_)).

% System predicates

system_type_annot(=, [tyvar(A), tyvar(A)], unit).
system_type_annot(\=, [tyvar(A), tyvar(A)], unit).
system_type_annot(==, [tyvar(A), tyvar(A)], unit).
system_type_annot(\==, [tyvar(A), tyvar(A)], unit).
system_type_annot(!, [], unit).
system_type_annot(\+, [unit], unit).
system_type_annot(true, [], unit).
system_type_annot(fail, [], unit).
system_type_annot(is, [int, int], unit).
system_type_annot(+, [int, int], int).
system_type_annot(-, [int, int], int).
system_type_annot(*, [int, int], int).
system_type_annot(/, [int, int], int).
system_type_annot(<, [int, int], unit).
system_type_annot(=<, [int, int], unit).
system_type_annot(>, [int, int], unit).
system_type_annot(>=, [int, int], unit).
system_type_annot(',', [unit, unit], unit).
system_type_annot([], [], list(tyvar(_A))).
system_type_annot('[|]', [tyvar(A), list(tyvar(A))], list(tyvar(A))).
system_type_annot(length, [list(tyvar(_A)), int], unit).

no_type_redef :-
   forall(system_type(T),
      ((\+decltype(T, _, _));
       write("redefined type "), write(T), nl, !, fail)
   ).

def_typeannot_pred(Con, ArgLen) :- typeannot(Con, Args), length(Args, ArgLen).

def_decltype_pred(Con, ArgLen) :- decltype(_, Con, Args), length(Args, ArgLen).

def_system_typeannot_pred(Con, ArgLen) :- system_type_annot(Con, Args, _), length(Args, ArgLen).

no_pred_type_annot_clash :-
   forall(def_typeannot_pred(Con,ArgLen),
      (\+def_decltype_pred(Con,ArgLen), \+def_system_typeannot_pred(Con, ArgLen)) ;
       type_annot_clash(Con, ArgLen)
      ),
   forall(def_decltype_pred(Con, ArgLen),
      (\+def_typeannot_pred(Con, ArgLen), \+def_system_typeannot_pred(Con, ArgLen)) ;
       type_annot_clash(Con, ArgLen)
      ),
   forall(def_system_typeannot_pred(Con, ArgLen),
      (\+def_typeannot_pred(Con, ArgLen), \+def_decltype_pred(Con, ArgLen)) ;
       type_annot_clash(Con, ArgLen)
      ).

type_annot_clash(Con, ArgLen) :-
   write("predicate "), write(Con/ArgLen), write(" defined as more than one of:"), nl,
   tab(3), write("typeannot, decltype, system_type_annot"), nl,
   !, fail.

no_double_typeannot :-
   forall((typeannot(Pred, Tys), length(Tys, TyLen)),
      (\+ (typeannot(Pred, Tys2), length(Tys2, TyLen), Tys \= Tys2)) ;
       (write("more than one type annotation for "), write(Pred/TyLen), nl,
       !, fail)
       ).

no_wrong_typeannot :-
  forall(
    current_predicate(typeannot/N),
    (N = 2 ; (typeannot_error(
      typeannot/N,
      "A type annotation must have two parameters."
      ),
      !, fail))),
  forall(
    (typeannot(Pred, Tys)),
    (
      (atom(Pred) ; (typeannot_error(
          typeannot(Pred, Tys),
          "The first argument must be an atom corresponding to the name of a predicate."),
        !, fail)),
      (is_list(Tys) ; (typeannot_error(
          typeannot(Pred, Tys),
          "The second argument must be a list of parameter types."),
        !, fail))
    )).

typeannot_error(TypeAnnot, ErrMsg) :-
  write("Error on type anotation "), write(TypeAnnot), nl,
  write(ErrMsg), nl.

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

new_inst_tyvars_cxt(Cxt, tyvar(In), Out) :- !,
  tyvar_cxt_lookup(Cxt, tyvar(In), Out).
new_inst_tyvars_cxt(Cxt, In, Out) :-
  In =.. [P| Args], new_inst_tyvars_list_cxt(Cxt, Args, NArgs),
  Out =.. [P| NArgs].

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
  X == Y, !, T1 = T2.

context_write([(X, _)|Context], Y, T) :-
  X \== Y, context_write(Context, Y, T).

checkparams(_Context, [], []).
checkparams(Context, [X|Xs], [Ty|Tys]) :-
  hastype(Context, X, Ty),
  checkparams(Context, Xs, Tys).

hastype(Context, A, T) :-
  var(A), !,
  context_write(Context, A, T).

hastype(_Context, A, int) :-
  integer(A), !.

hastype(Context, A, Ret) :-
  A =.. [B|Params], (atom(B); B == []), !,
  ((typeannot(B, Ty), RetV = unit) ;
          system_type_annot(B, Ty, RetV);
          decltype(RetV, B, Ty)),
  new_inst_tyvars_list_cxt(Cxt, Ty, Ty2),
  new_inst_tyvars_cxt(Cxt, RetV, Ret2),
  set_check_predicate(B, A, Ty, RetV),
  Ret2 = Ret,
  checkparams(Context, Params, Ty2).

zip([], [], _Zs).
zip([X|Xs], [Y|Ys], [Z|Zs]) :-
  Z = (X,Y),
  zip(Xs, Ys, Zs).

initcontext(Params, Tys, Context) :-
  zip(Params, Tys, Context).

checkrules :-
  no_wrong_typeannot,
  no_type_redef,
  no_pred_type_annot_clash,
  no_double_typeannot,
  forall(
    (typeannot(Id, Ty), atom(Id)),
    check_type(Id, Ty) ;
      (write_error, !, fail)
  ).

check_type(Id, Ty) :-
  length(Ty, TyLength), %prettyprint(Id, Ty),
      functor(Head, Id, TyLength),
      forall(
        clause(Head, Body),
        (Head =.. [Pred|Params],
         normalize(Params, Body, NParams, NBody),
         NHead =.. [Pred|NParams],
         set_checking(Head, Body, Ty, NHead, NBody),
         initcontext(NParams, Ty, Context),
         hastype(Context, NBody, _T)
        )
      ).

write_error :-
   write("Error while checking: "), nl,
   is_checking(Head, Body, Ty, NHead, NBody),
   write_rule(Head, Body),
   write("with type: "), nl,
   tab(3), write(Ty), nl,
   write("normalized to"), nl,
   write_rule(NHead, NBody),
   retract(checking_preds(CList, EList)),
   write_checked_path(CList),
   write_error_path(EList).

write_rule(Head, Body) :-
   tab(2), write(Head), write(" :- "), nl,
   tab(5), write(Body), nl.

write_error_path([(Rule, ArgTys, RetTy) | PLT1] - PLT2) :-
   var(PLT2), !,
   tab(2), write("Error may be in Rule:"), nl,
   tab(3), write(Rule), nl,
   tab(2), write("expected type:"), nl,
   tab(3), write(ArgTys), write(" -> "), write(RetTy), nl,
   write_error_path(PLT1 - PLT2).

write_error_path(DL - DL) :-
   var(DL), !.

write_checked_path([(Rule, _A, _R) | PLT1] - PLT2) :-
   var(PLT2), !,
   write("checked: "), write(Rule), nl,
   write_checked_path(PLT1 - PLT2).

write_checked_path(DL - DL) :-
   var(DL), !.

cleanup_dynamic :-
   forall(is_checking(H, B, T, NH, NB),
            retract(is_checking(H, B, T, NH, NB))),
   forall(checking_preds(CL, EL),
           retract(checking_preds(CL, EL))),
   assert(checking_preds(CLT - CLT, ELT - ELT)).

set_checking(Head, Body, Ty,  NHead, NBody) :-
   cleanup_dynamic,
   assert(is_checking(Head, Body, Ty, NHead, NBody)).

set_check_predicate(',', _Rule, _ArgTys, _RetTy) :-
   !,
   retract(checking_preds(CL - CLT, EL - ELT)),
   CLT = EL,
   assert(checking_preds(CL - ELT, NL - NL)).

set_check_predicate(_Pred, Rule, ArgTys, RetTy) :-
   retract(checking_preds(CL - CLT, EL - ELT)),
   ELT = [(Rule, ArgTys, RetTy) | NewELT],
   assert(checking_preds(CL - CLT, EL - NewELT)).

prettyprint(Id, Ty) :-
  write(Id), write(" : "), write(Ty), nl.

samelength(XS, YS) :- length(XS, N), length(YS, N).

%?- current_predicate(p/X).
%X = 1 ;
%X = 2 ;
%false.
