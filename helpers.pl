:- use_module(library(clpfd)).

set_A(N, Set) :- 
    High is N * 2 + 2,
    X in 4..High,
    findall(X, indomain(X), Set).

set_B(N, Set) :-
    set_A(N, A_n),
    N1 is N + 1,
    set_A(N1, A_n1),
    subtract(A_n1, A_n, Set).

all_sets(N, Pred, Answer) :-
    X in 1..N, indomain(X),
    call(Pred, X, Answer).

zip(X, Y, [X, Y]).

join(_, [X], X) :- !.
join(Sep, [X | Xs], S) :-
    join(Sep, Xs, Sx),
    string_concat(Sep, Sx, Sy),
    string_concat(X, Sy, S).

question_1(Na, Nb, As, Bs):-
    findall(As, all_sets(Na, set_A, As), As),
    findall(Bs, all_sets(Nb, set_B, Bs), Bs),
    X in 1..Na,
    Y in 1..Nb,
    findall(X, indomain(X), Nas),
    findall(Y, indomain(Y), Nbs),
    maplist(join(','), As, Jas),
    maplist(join(','), Bs, Jbs),
    maplist(zip, Nas, Jas, Zas),
    maplist(zip, Nbs, Jbs, Zbs),
    maplist(format('$A_~p=\\{~p\\}$~n'), Zas),
    maplist(format('$B_~p=\\{~p\\}$~n'), Zbs).

%% Assignment 2

cross(Set, (A, B)) :- member(A, Set), member(B, Set).

pairs(Set, Pairs) :- findall(X, cross(Set, X), Pairs).

reflexive([], _) :- !.
reflexive([X | Xs], Relation) :-
    member((X, X), Relation), reflexive(Xs, Relation).

symmetric(Relation) :-
    Relation = [] ; symmetric(Relation, Relation).
symmetric([], _) :- !.
symmetric([(X, Y) | Xs], Relation) :-
    member((Y, X), Relation), symmetric(Xs, Relation).

antisymmetric(Relation) :-
    Relation = [] ; antisymmetric(Relation, Relation).
antisymmetric([], _) :- !.
antisymmetric([(X, Y) | Xs], Relation) :-
    ( \+ member((Y, X), Relation) ; X = Y ),
    antisymmetric(Xs, Relation).

transitive(Relation) :-
    forall((member((X, Y), Relation), member((Y, Z), Relation)),
           member((X, Z), Relation)).

equivalence(Set, Relation) :-
    reflexive(Set, Relation),
    symmetric(Relation),
    transitive(Relation).

pair(X, Xs, (X, Y)) :- member(Y, Xs).

relproduct_helper([], _, []) :- !.
relproduct_helper([(X, Y) | R1], R2, [Pair | R]) :-
    findall(Z, member((Y, Z), R2), Z),
    findall(Pair, pair(X, Z, Pair), Pair),
    relproduct_helper(R1, R2, R).
relproduct(R1, R2, R) :-
    relproduct_helper(R1, R2, Raw),
    flatten(Raw, Flat),
    list_to_set(Flat, R).

relation_S(Set, S) :- pairs(Set, Pairs), pairs(Pairs, S).

%% relation_RR(S, RR) :-
%%     relproduct(S, S, R),
%%     exclude(=(R), 
