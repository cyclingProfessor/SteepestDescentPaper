
improve(SeqLength,List) :-
        setup(f), setup(h),
        sequence(8,SeqLength,List).


%  Input scoring for f 
lookup(f,S) :-
S = []([]( 0, 4, 6, 0, 0, 0, 0, 0, 0, 0), 
       []( 0, 4, 6, 0, 0, 0, 0, 0, 0, 0), 
       [](13, 0, 0, 0, 0, 8, 0, 0, 0, 0), 
       [](13, 0, 8, 0, 0, 12, 0, 0, 0, 0), 
       []( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), 
       []( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), 
       []( 0, 0, 7, 0, 0, 0, 0, 0, 0, 0), 
       []( 0, 0, 23, 0, 0, 0, 0, 0, 0, 0), 
       [](14, 0, 0, 0, 0, 0, 0, 0, 0, 0), 
       []( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)).
% Input scoring for h
lookup(h,H) :-
       H = [](0, 0, 0, 0, 1, 0, 0, 5, 0, 0).

% [First|Rest] is the sequence of improving codes we are seeking
% Length is the length of this sequence
% For input 8, a code is simply an array of symbols such as: <0,0,1,0,1,C,0,0>
% For codes of this size, the number of improving codes should be 1785
sequence(N, SeqLength, [First|Rest]) :-
        zeroise(N,First), 
        M is N+1,
        ls(M,First,0,Rest),   % Recurse on finding the next code
        SeqLength is length(Rest)+1,  % Return the length of the list of codes
        writelist([First|Rest]).

% Stop improving at the code <0,C,0,0,0,0,0,0>
ls(M,This,_,[This,Final]) :-
        arg(2,This,c),
        (for(I,3,M),param(This) do arg(I,This,0)), !,
        functor(Final,[],M),
        (for(I,1,M),param(Final) do arg(I,Final,0)),
        setarg(2,Final,1).  % Set the final code to <0,1,0,0,0,0,0,0>

% For other codes, find the next improving code, and its value, and recurse
ls(M,This,Val,[This|Rest]) :-
        move(M,This,Val,Next,NextVal), !,
        ls(M,Next,NextVal,Rest).

% Find the best move, and do that move
move(M,This,Val,New,NewVal) :-
        best_move(M,This,Val,NewI-NewSym-NewVal),
        chg(This,NewI,NewSym,New).

% Do a move by copying A (This) to B (New) and then setting the Ith symbol to Sym.
chg(A,I,Sym,B) :-
        functor(A,F,N), functor(B,F,N),
        (foreacharg(X,A), foreacharg(Y,B) do X=Y),
        setarg(I,B,Sym).

% Find all the possible moves and choose the one that yields the highest value
best_move(M,This,Val,Best) :-
        findall(I-Sym-TryVal, better_code(M,This,Val,I,Sym,TryVal), List),
        my_get_max(List,Best).   % Select the best move from the
                                 % resulting List

better_code(M,This,Val,I,Sym,TryVal) :-
       inlist(I,2,M),   % Choose a symbol in the code
       OldSym is This[I],
       flip(OldSym,Sym),   % Flip it to a new symbol
       chg(This,I,Sym,Try),  
       compval(M,Try,TryVal),  % Evaluate the new code
       TryVal>Val.  % Keep it if it's better than the old code

% Choose any value between Min and Max
inlist(X,X,_).
inlist(X,Min,Max) :- Min<Max,Next is Min+1, inlist(X,Next,Max).

% Calculate all the f(X,Y) values in the current codelist, and
% multiply them by the appropriate power of 4
compval(M,A,Val) :-
        (for(I,1,M-1),fromto(0,TS,NS,Val1),param(A,M) 
        do
            A1 is A[I], A2 is A[I+1],
            Weight is 4^(M-(I+1)),
            once(f(A1,A2,FC)),
            NS is TS+Weight*FC %+GC
        ),
% and find the h value for the last code in the list
        AM is A[M],
        h(AM,HC),
% and add them
        Val is Val1+HC. 

% Each entry has the index of the symbol to be changed, its new value
% and the value of the resulting code.
% This predicate seeks the triple with the highest value
my_get_max([First|Rest],Best) :-
        First=_-_-OldVal,
        gm(OldVal,First,Rest,Best).

gm(_,This,[],This).
gm(OldVal,This,[Next|Rest],Best) :-
        Next=_-_-Val,
        (Val>OldVal -> gm(Val,Next,Rest,Best) 
        ; 
                       gm(OldVal,This,Rest,Best)
        ).

% Intialize the code to <0,0,0,0,0,0,0,0>
% - encoded as an ECLiPSe array: [](0,0,0,0,0,0,0,0)
zeroise(N,First) :-
        M is N+1,
        functor(First,[],M),
        (for(I,1,M),param(First) do arg(I,First,0)).        
writelist(List) :- (foreach(E,List) do writeln(E)).

% Translate each symbol to an index, 
% for looking up the values of f and h
sym1(0,1).
sym1(1,2).
sym1(c,3).
sym1(x,4).
sym1(0-1,5).
sym1(0-c,6).
sym1(0-x,7).
sym1(1-c,8).
sym1(1-x,9).
sym1(c-x,10).

flip(X,X-Y) :- atomic(X), sym1(X-Y,_).
flip(X,Y-X) :- atomic(X), sym1(Y-X,_).
flip(X-Y,Z) :- Z=X ; Z=Y.

% Look up the f-value
f(X,Y,C) :- sym1(X,I),sym1(Y,J), getval(s(I,J),C).
% Look up the h value
h(Y,C) :-   sym1(Y,J), getval(h(J),C).

% Setup f and h as ECLiPSe stored arrays
setup(f) :-
        lookup(f,S), 
        dim(S,[R,C]),R1 is R+1, C1 is C+1,
        (local array(s(R1,C1))),
         (multifor([I,J],[1,1],[R,C]),param(S) 
            do V is S[I,J], setval(s(I,J),V)
         ).

setup(h) :- lookup(h,H),
        dim(H,[R2]),R3 is R2+1,
        (local array(h(R3))),
         (for(J,1,R2), param(H)
         do
             V is H[J], setval(h(J),V)
        ).
