:- multifile(typeannot/2).

% Wrong arity
%typeannot.
%typeannot(foo).
%typeannot(foo, bar, baz).
%typeannot(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15).

% Wrong first parameter
%typeannot(foo(0), []).
%typeannot(foo(a), []).
%typeannot(1, []).

% Wrong second parameter
%typeannot(foo, bar(0)).
%typeannot(foo, bar(a)).
%typeannot(foo, 1).
%typeannot(foo, int).
