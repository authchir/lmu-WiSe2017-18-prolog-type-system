:- multifile(typeannot/2).
:- multifile(decltype/3).

decltype(mylist(tyvar(_A)), nil, []).
decltype(mylist(tyvar(A)), cons, [tyvar(A), mylist(tyvar(A))]).

typeannot(mylistLen, [mylist(tyvar(_A)), int]).

%mylistLen(0, 0).
mylistLen(nil, 0).
mylistLen(cons(_, Tail), N) :- mylistLen(Tail, N2), N is N2 + 1.

