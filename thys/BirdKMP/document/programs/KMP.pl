% -*- mode: prolog -*-
% Bird's Morris-Pratt string matcher
% Chapter 17, "Pearls of Functional Algorithm Design", 2010.
%   - adapted to use rational trees.
%   - with the `K' (next) optimisation
% Tested with SWI Prolog, which has good support for rational trees.

% root/2 (+, -) det
root(Ws, T) :- grep(T, null, Ws, T).

% op/4 (?, +, +, -) det <-- Root may or may not be fully ground
op(Root, null,                _X, Root).
op(Root, node([],      L, _R), X, T) :- op(Root, L, X, T).
op(Root, node([V|_Vs], L,  R), X, T) :-
    (X = V -> T = R ; op(Root, L, X, T)).

% next/3 (+, +, -) det
next(_X, null,               null).
next(_X, node([], L, R),     node([], L, R)).
next( X, node([V|Vs], L, R), T) :- ( X = V -> T = L ; T = node([V|Vs], L, R) ).

% grep/4 (+, +, +, -) det
grep(_Root, L, [],     node([], L, null)).
grep( Root, L, [V|Vs], node([V|Vs], L1, R)) :-
    next(V, L, L1), op(Root, L, V, T), grep(Root, T, Vs, R).

% ok/1 (+) det
ok(node([],  _L, _R)).

%% Driver

% matches_aux/5 (+, +, +, +, -) det
matches_aux(_Root, N, T, [],     Ns) :- ( ok(T) -> Ns = [N] ; Ns = [] ).
matches_aux( Root, N, T, [X|Xs], Ns) :-
    N1 is N + 1, op(Root, T, X, T1),
    ( ok(T) -> ( Ns = [N|Ns1], matches_aux(Root, N1, T1, Xs, Ns1) )
             ; matches_aux(Root, N1, T1, Xs, Ns) ).

% matches/3 (+, +, -) det
matches(Ws, Txt, Ns) :- root(Ws, Root), matches_aux(Root, 0, Root, Txt, Ns).

% :- root([1,2,1], Root).
% :- root([1,2,1,1,2], Root).
% :- matches([1,2,3,1,2], [1,2,1,2,3,1,2,3,1,2], Ns).
