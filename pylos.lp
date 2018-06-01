:- use_module(library(clpfd)).

% Pylos Strategy Guide
% Pylos is an abstract strategy game for two players. 
% 0. Each player takes turns placing a black or white marble onto a 4x4 grid (the bottom level), or on top of 
% four other marbles as part of another level. 
% 1. If a player has no marbles left, they lose.
% 2. Whoever can place a marble on the top of the pyramid wins. 
% 3. If it is possible to move a marble already on the board to a higher level, the player may do so. 
% 4. If a player creates a 2x2 square of their color, they may take up to 2 marbles off the board and put them
% back in their collection.

% The notation is  Column-Row-Level where
% the columns start from the left, 1-4; the rows start at the top, 1-4, & the level a is the bottom level, a-d.

%                      Level a                           Level b                    Level c             Level d 
%Column      1       2       3       4             1       2       3               1       2               1    
%        *-------------------------------*     *-----------------------*       *---------------*       *-------*
%Row   1 |  a11  |  a12  |  a13  |  a14  |     |  b11  |  b12  |  b13  |       |  c11  |  c12  |       |  d11  |
%        |-------------------------------|     |-----------------------|       |---------------|       *-------*
%Row   2 |  a21  |  a22  |  a23  |  a24  |     |  b21  |  b22  |  b23  |       |  c21  |  c22  |
%        |-------------------------------|     |-----------------------|       *---------------*
%Row   3 |  a31  |  a32  |  a33  |  a34  |     |  b31  |  b32  |  b33  |
%        |-------------------------------|     *-----------------------*
%Row   4 |  a41  |  a42  |  a43  |  a44  |
%        *-------------------------------*


%State:[
%       [[_,_,_,_],[_,_,_,_],[_,_,_,_],[_,_,_,_]],
%       [[_,_,_],[_,_,_],[_,_,_]],
%       [[_,_],[_,_]],
%       [[_]] ].

% For writing into the file:
% ?- protocol('filename.ext').
% For stopping the writing from the console.
% ?- noprotocol.

% For more info: http://www.swi-prolog.org/pldoc/man?section=allsolutions
% ?- tell('filename.ext').
% ?- told.
% ?- see('filename.ext').
% ?- seen.

% For writng SHA HASH values for each state.
% ?- sha_hash(Flat,H,[]), hash_atom(H,Hex).

%---------------------- STRUCTURES ------------------------
:- dynamic ball/2.

stackUp([A,B,C,D]) :-
   %flatten([A,B,C,D],Flat),

   A = [[A11,A12,A13,A14],[A21,A22,A23,A24],[A31,A32,A33,A34],[A41,A42,A43,A44]],
   B = [[B11,B12,B13],[B21,B22,B23],[B31,B32,B33]],
   C = [[C11,C12],[C21,C22]],
   D = [[D11]],

   retractall(ball(_,_)),
   assert(ball(1,A11)), assert(ball(2,A12)), assert(ball(3,A13)), assert(ball(4,A14)), 
   assert(ball(5,A21)), assert(ball(6,A22)), assert(ball(7,A23)), assert(ball(8,A24)), 
   assert(ball(9,A31)), assert(ball(10,A32)), assert(ball(11,A33)), assert(ball(12,A34)), 
   assert(ball(13,A41)), assert(ball(14,A42)), assert(ball(15,A43)), assert(ball(16,A44)), 

   SqB11 = [A11,A12,A21,A22], SqB12 = [A12,A13,A22,A23], SqB13 = [A13,A14,A23,A24],
   SqB21 = [A21,A22,A31,A32], SqB22 = [A22,A23,A32,A33], SqB23 = [A23,A24,A33,A34],
   SqB31 = [A31,A32,A41,A42], SqB32 = [A32,A33,A42,A43], SqB33 = [A33,A34,A43,A44],

   SqC11 = [B11,B12,B21,B22], SqC12 = [B12,B13,B22,B23], SqC21 = [B21,B22,B31,B32], SqC22 = [B22,B23,B32,B33],

   SqD11 = [C11,C12,C21,C22], 

   (member(0,[B11|SqB11]) -> I#=1; assert(ball(17,B11))), 
   (member(0,[B12|SqB12]) -> I#=1; assert(ball(18,B12))), 
   (member(0,[B13|SqB13]) -> I#=1; assert(ball(19,B13))),
   
   (member(0,[B21|SqB21]) -> I#=1; assert(ball(20,B21))), 
   (member(0,[B22|SqB22]) -> I#=1; assert(ball(21,B22))), 
   (member(0,[B23|SqB23]) -> I#=1; assert(ball(22,B23))),   
   
   (member(0,[B31|SqB31]) -> I#=1; assert(ball(23,B31))), 
   (member(0,[B32|SqB32]) -> I#=1; assert(ball(24,B32))), 
   (member(0,[B33|SqB33]) -> I#=1; assert(ball(25,B33))),
   
   (member(0,[C11|SqC11]) -> I#=1; assert(ball(26,C11))), 
   (member(0,[C12|SqC12]) -> I#=1; assert(ball(27,C12))), 
   (member(0,[C21|SqC21]) -> I#=1; assert(ball(28,C21))), 
   (member(0,[C22|SqC22]) -> I#=1; assert(ball(29,C22))),
   
   (member(0,[D11|SqD11]) -> I#=1; assert(ball(30,D11))),

   retractall(ball(_,0)).

% State=[1,2,1,2,2,1,1,2,1,1,2,2,2,2,1,1,0,1,2,2,2,2,1,2,0,0,2,1,0,0]
% legalState: true if [A,B,C,D] is legal.
legalState([A,B,C,D]) :-
   %State = [R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30],
   flatten([A,B,C,D],Flat), Flat ins 0..2,
   onBoard(Flat,NBalls),
   findall(I,ball(I,_),Bag), length(Bag,NBalls).

% calculates the no of ball on the board
onBoard([],0).
onBoard([H|T], N) :- H #= 0, onBoard(T,N).
onBoard([H|T], N) :-
   H #\= 0, N #= N1 + 1,
   onBoard(T, N1).
%----------------------- LABELING -------------------------


%----------------------- THE GAME -------------------------

search :-
   Start = [[[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0],[0,0]],[[0]]],
   gameON(Start, 1, [Start], 15, 15).

% where Player 1 wins
gameON(_, _, Visited, _, 0) :-
   write('Game Over'), nl, write('Winner: 1'), nl,
   reverse(Visited,V), writeStates(V,1).

% where Player 1 actually plays
gameON(Current, 1, Visited, Bo1, Bo2) :- 
   Bo1 #>  0, Bo2 #> 0,
   turn(Current, 1, Next), \+ member(Next,Visited),
   ballsOnBoard(1,Next,N1), B1 #= 15 - N1,
   ballsOnBoard(2,Next,N2), B2 #= 15 - N2,
   gameON(Next, 2, [Next |Visited], B1, B2).

% where Player 2 wins
gameON(_, _, Visited, 0, _) :-
   write('Game Over'), nl, write('Winner: 2'), nl,
   reverse(Visited,V), writeStates(V,1).

% where Player 2 actually plays
gameON(Current, 2, Visited, Bo1, Bo2) :-
   Bo1 #>  0, Bo2 #> 0,
   turn(Current, 2, Next), \+ member(Next,Visited),
   ballsOnBoard(1,Next,N1), B1 #= 15 - N1,
   ballsOnBoard(2,Next,N2), B2 #= 15 - N2,
   gameON(Next, 1, [Next |Visited], B1, B2).

% In state State, Player has N balls on the board. 
ballsOnBoard(Player, State, N) :-
   flatten(State, Flat),
   findall(Player, member(Player, Flat), Bag), 
   length(Bag, N).

% Writes States in proper sequence.
writeStates([],_) :- nl.
writeStates([H|T],N) :- 
   write('State '), write(N), write(': '),
   N1 #= N + 1, writeList(H), writeStates(T,N1).
   
% Reverse-accumulate
reverse(Xs,Ys) :- reverse(Xs,[],Ys).
reverse([],Ys,Ys).
reverse([X|Xs],Acc,Ys) :- reverse(Xs,[X|Acc],Ys).

%------------------------ TURN 1 --------------------------
% Combination of TURN 3 and then TURN 2: without placing a ball, 
% you get to remove 2 balls from the board.

% Case 1: when Player tranfers to B, Player can addBall to B AND remove from A.
turn(Current, Player, Next) :-
   range(17,25,BIndices), member(Nb,BIndices),
   addBallN(Nb, Current, Player, Temp1),

   range(1,16,AIndices), member(Na,AIndices),
   removeBallN(Na, Temp1, Player, Temp2),

   hasSquare(Temp2, Player),
   findall(State, remove2Balls(Temp2, Player, State), Bag),
   list_to_set(Bag,NoDuplicates),
   member(Next,NoDuplicates).
   %Current #\= Next. % trivial

% Case 2: when Player tranfers to C, Player can addBall to C AND remove from B or A.
turn(Current, Player, Next) :-
   range(26,29,CIndices), member(Nc,CIndices),
   addBallN(Nc, Current, Player, Temp1), 
   
   range(1,25,ABIndices), member(Nab,ABIndices),
   removeBallN(Nab, Temp1, Player, Temp2),

   hasSquare(Temp2, Player),
   findall(State, remove2Balls(Temp2, Player, State), Bag),
   list_to_set(Bag,NoDuplicates),
   member(Next,NoDuplicates).
   %Current #\= Next. % trivial

%------------------------ TURN 2 --------------------------
% Where the Player removes two free-balls of his own by adding 
% a ball as he/she forms a square, to get the Next legal state.
turn(Current, Player, Next) :-
   addBall(Current, Player, Temp),
   hasSquare(Temp, Player),
   findall(State, remove2Balls(Temp, Player, State), Bag),
   list_to_set(Bag,NoDuplicates),
   member(Next,NoDuplicates).
   %Current #\= Next. % trivial
   
%------------------------ TURN 3 --------------------------
% when Player uses a free-ball to place on the next higher level.
% There exists only two cases:
% Case 1: when Player tranfers to B, Player can addBall to B AND remove from A.
turn([A,B,C,D], Player, [P,Q,R,S]) :-
   range(17,25,BIndices), member(Nb,BIndices),
   addBallN(Nb, [A,B,C,D], Player, Temp),

   range(1,16,AIndices), member(Na,AIndices),
   removeBallN(Na, Temp, Player, [P,Q,R,S]).

% Case 2: when Player tranfers to C, Player can addBall to C AND remove from B or A.
turn([A,B,C,D], Player, [P,Q,R,S]) :-
   range(26,29,CIndices), member(Nc,CIndices),
   addBallN(Nc, [A,B,C,D], Player, Temp), 
   
   range(1,25,ABIndices), member(Nab,ABIndices),
   removeBallN(Nab, Temp, Player, [P,Q,R,S]).

%------------------------ TURN 4 --------------------------
% simply adds a ball of the Player to form the Next legal state from the Current state.
turn(Current, Player, Next) :- 
   addBall(Current, Player, Next).

%------------------ ADDITION OF A BALL --------------------

% adds ball in State [A,B,C,D] of the Player to give state [P,Q,R,S]
addBall([A,B,C,D], Player, [P,Q,R,S]) :-
   flatten([A,B,C,D],Flat), %writeList(Flat),
   select(0,Flat, Player, Result), %built-in or may use replace/4
   Result = [R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30],
   P = [[R1,R2,R3,R4],[R5,R6,R7,R8],[R9,R10,R11,R12],[R13,R14,R15,R16]],
   Q = [[R17,R18,R19],[R20,R21,R22],[R23,R24,R25]],
   R = [[R26,R27],[R28,R29]],
   S = [[R30]],
   stackUp([P,Q,R,S]), legalState([P,Q,R,S]).

% adds ball at Nth position in State [A,B,C,D] of the Player to give state [P,Q,R,S]
addBallN(N, [A,B,C,D], Player, [P,Q,R,S]) :-
   flatten([A,B,C,D],Flat), %writeList(Flat),
   nth1(N,Flat,0), 
   select(0,Flat, Player, Result),
   nth1(N,Result,Player),
   Result = [R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30],
   P = [[R1,R2,R3,R4],[R5,R6,R7,R8],[R9,R10,R11,R12],[R13,R14,R15,R16]],
   Q = [[R17,R18,R19],[R20,R21,R22],[R23,R24,R25]],
   R = [[R26,R27],[R28,R29]],
   S = [[R30]],
   stackUp([P,Q,R,S]), legalState([P,Q,R,S]).

%------------------- OTHER PREDICATES ---------------------

% State [A,B,C,D] has a square of the Player, e.g. [2,2,2,2].
hasSquare([A,B,C,D], Player) :-
   A = [[A11,A12,A13,A14],[A21,A22,A23,A24],[A31,A32,A33,A34],[A41,A42,A43,A44]],
   B = [[B11,B12,B13],[B21,B22,B23],[B31,B32,B33]],
   C = [[C11,C12],[C21,C22]],
   %D = [[D11]], % No need I guess
   D = [[0]], % trivial

   SqB11 = [A11,A12,A21,A22], SqB12 = [A12,A13,A22,A23], SqB13 = [A13,A14,A23,A24],
   SqB21 = [A21,A22,A31,A32], SqB22 = [A22,A23,A32,A33], SqB23 = [A23,A24,A33,A34],
   SqB31 = [A31,A32,A41,A42], SqB32 = [A32,A33,A42,A43], SqB33 = [A33,A34,A43,A44],

   SqC11 = [B11,B12,B21,B22], SqC12 = [B12,B13,B22,B23], SqC21 = [B21,B22,B31,B32], SqC22 = [B22,B23,B32,B33],

   SqD11 = [C11,C12,C21,C22],

   % 14 possible square positions
   Squares = [SqB11, SqB12, SqB13, SqB21, SqB22, SqB23, SqB31, SqB32, SqB33, SqC11, SqC12, SqC21, SqC22, SqD11],
   % square is present in Squares
   member([Player, Player, Player, Player],Squares).

%----------------- REMOVAL OF THE BALLS -------------------

% Next is the state you get on removing 2 free-balls one by one from the State.
remove2Balls(State, Player, Next) :-
   removeBall(State, Player, Temp),
   removeBall(Temp, Player, Next).

% [P,Q,R,S] is resulting state after removal of ONE ball of the Player from [A,B,C,D].
removeBall([A,B,C,D], Player, [P,Q,R,S]) :-
   flatten([A,B,C,D],Flat), %writeList(Flat),
   select(Player, Flat, 0, Result), %built-in or may use replace/4
   Result = [R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30],
   P = [[R1,R2,R3,R4],[R5,R6,R7,R8],[R9,R10,R11,R12],[R13,R14,R15,R16]],
   Q = [[R17,R18,R19],[R20,R21,R22],[R23,R24,R25]],
   R = [[R26,R27],[R28,R29]],
   S = [[R30]],
   stackUp([P,Q,R,S]), legalState([P,Q,R,S]).

% [P,Q,R,S] is resulting state after removal of ONE ball, at Nth position, of the Player from [A,B,C,D].
removeBallN(N, [A,B,C,D], Player, [P,Q,R,S]) :-
   flatten([A,B,C,D],Flat), %writeList(Flat),
   nth1(N,Flat,Player),
   select(Player, Flat, 0, Result), %built-in or may use replace/4
   nth1(N,Result,0),
   Result = [R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30],
   P = [[R1,R2,R3,R4],[R5,R6,R7,R8],[R9,R10,R11,R12],[R13,R14,R15,R16]],
   Q = [[R17,R18,R19],[R20,R21,R22],[R23,R24,R25]],
   R = [[R26,R27],[R28,R29]],
   S = [[R30]],
   stackUp([P,Q,R,S]), legalState([P,Q,R,S]).

% *** NOTE: ADDITION/ REMOVAL always results in LEGAL STATE ***

%-------------------- OLD PREDICATES ----------------------

% writes the List on a new-line
writeList([]) :- nl.
writeList([H|T]) :- write(H), write(' '), writeList(T).

%writes each nested list in the List. 
writeLL([]).
writeLL([H|T]) :- writeList(H), writeLL(T).

% select(X,List,R): R is a List with one removed X
select(X,[X|T],T).
select(X,[H|T],[H|R]) :- %X \= H, 
   select(X,T,R).

% substitute(Old,New,OldList,NewList): NewList is the result
% of replacing ALL occurrences of Old in OldList by New.
substitute(_,_,[],[]). 

substitute(X,Y,[X|T1],[Y|T2]) :-
   substitute(X,Y,T1,T2).

substitute(X,Y,[Z|T1],[Z|T2]) :-
   Z \= X,
   substitute(X,Y,T1,T2).

% replace(Old,New,OldList,NewList): NewList is the result
% of replacing ONE occurrence of Old in OldList by New.
replace(X,Y,[X|T1],[Y|T1]).
   
replace(X,Y,[Z|T1],[Z|T2]) :-
   %Z #\= X,
   replace(X,Y,T1,T2).

% range(M,N,List): List is list of integers [M,N], M<N.
range(N,N,[N]).
range(M,N,[M|Ns]) :- 
   M < N, M1 is M+1, range(M1,N,Ns).

%----------------------------------------------------------