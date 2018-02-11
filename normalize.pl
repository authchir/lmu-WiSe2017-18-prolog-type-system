% normalize.pl

normalize([Pred|HeadArgs], Body, [Pred|NewHeadArgs], NewBody) :- 
   normalize_arg_list(HeadArgs, NewHeadArgs, BLT - BLT, BodyList - NBLT),
   NBLT = Body, NewBody = BodyList.
  
normalize_arg_list([], [], BodyList - BLT, BodyList - BLT).
normalize_arg_list([Arg|Args], [NArg|NArgs], BodyList - BLT, BodyList - NBLT) :-
   normalize_arg(Arg, NArg, BodyList - BLT, BodyList - BLT2), 
   normalize_arg_list(Args, NArgs, BodyList - BLT2, BodyList - NBLT).

normalize_arg(Arg, NewArg, BodyList - BLT, BodyList - BLT) :-
   var(Arg), !, Arg = NewArg.

normalize_arg(Arg, NewArg, BodyList - BLT, BodyList - NBLT) :- 
   NewArg = X, BLT = [(X = Arg)|NBLT].
