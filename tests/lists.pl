:- multifile(typeannot/2).

typeannot(mylen1, [list(tyvar(_A)), int]).
mylen1(L, Len) :- L = [], Len = 0.
mylen1(L, Len) :- L = [_|T], mylen1(T, TLen), Len is TLen + 1.

typeannot(mylen, [list(tyvar(_A)), int]).
mylen([], 0).
mylen([_|T], Len) :- mylen(T, TLen), Len is TLen + 1.

typeannot(myappend1, [list(tyvar(A)), list(tyvar(A)), list(tyvar(A))]).
myappend1(XS, YS, ZS) :- XS = [], !, YS = ZS.
myappend1(XS, YS, ZS) :-
  XS = [X|XST], !,
  ZS = [X|ZST],
  myappend1(XST, YS, ZST).

typeannot(myappend, [list(tyvar(A)), list(tyvar(A)), list(tyvar(A))]).
myappend([], YS, YS).
myappend([X|XS], YS, [X|ZS]) :-
  myappend(XS, YS, ZS).

typeannot(myappend_length, []).
myappend_length :-
  XS = [1, 2, 3],
  YS = [4, 5, 6],
  mylen(XS, N1),
  mylen(YS, N2),
  myappend(XS, YS, ZS),
  N3 is N1 + N2,
  mylen(ZS, N3).

typeannot(mylen_multiple_instances, []).
mylen_multiple_instances :-
  mylen([1,2,3,4,5], 5),
  mylen([_A,_B,_C,_D,_E], 5),
  mylen([[],[],[],[],[]], 5),
  mylen([mylen([], 0), mylen([], 0)], 2).
  % Mixing types does not type check
  % mylen([0, []], 2).
