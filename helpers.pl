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

perm_element(Set, Element, Result) :-
    append(X, Y, Set), append([X, [Element], Y], Result).

permutations(Set, Powerset) :-
    perm_helper(Set, [[]], Powerset).
perm_helper([], X, X) :- !.
perm_helper([X | Xs], In, Out) :-
    findall(Res, 
            ( member(Sub, In), 
              findall(Res, perm_element(Sub, X, Res), Res) ),
            Res),
    append(Res, Flat),
    append([In, Flat], Total),
    perm_helper(Xs, Total, Out).

powerset(Set, Result) :-
    powerset_helper(Set, [[]], Result).
powerset_helper([], X, X) :- !.
powerset_helper([X | Xs], In, Result) :-
    findall(Z, (member(Y, In), append([X], Y, Z)), Z),
    append(In, Z, Next),
    powerset_helper(Xs, Next, Result).

like((X, X)).

likes(In, Pairs) :-
    pairs(In, Raw),
    include(like, Raw, Pairs).

query_parts(['[surname] LIKE "%~p%"',
             '[name] LIKE "%~p%"',
             '[midname] LIKE "%~p%"',
             'course="~p"',
             'group="~p"']).

tuple([], [], []) :- !.
tuple([X | Xs], [Y | Ys], [(X, Y) | Zs]) :- tuple(Xs, Ys, Zs).

exclude_query((false, _)).

interleave([X], _, X) :- !.
interleave([X | Xs], Glue, Result) :-
    interleave(Xs, Glue, Previous),
    format(atom(Result), "~p~p~p", [X, Glue, Previous]).

each(Elt, List, Predicate, Collector, Result) :-
    findall(Collector, (member(Elt, List), Predicate), Result).

%% build_query(fields(Surname, Name, Midname, Course, Group), Query) :-
%%     Fields = [Surname, Name, Midname, Course, Group],
%%     query_parts(Parts),
%%     tuple(Fields, Parts, Tuples),
%%     exclude(exclude_query, Tuples, Filtered),
%%     each((X, Y), Filtered, format(atom(Z), Y, [X]), Z, Disjoint),
%%     atomic_to_string(Disjoint, ' and ', Query).
%%     interleave(Disjoint, ' and ', Query).

%% ?- build_query(fields('Kaczynski', 'Ted', false, 'Number Theory', false), Q).
%% Q = '[surname] LIKE "%Kaczynski%" and [name] LIKE "%Ted%" and course="Number Theory"'.

plus(X, Y, Z) :- Z is X + Y.

reduce([], X, _, X) :- !.
reduce([X | Xs], Acc, Predicate, Result) :-
    call(Predicate, Acc, X, Interim), 
    reduce(Xs, Interim, Predicate, Result).
reduce([X | Xs], Predicate, Result) :- reduce(Xs, X, Predicate, Result).

mapconcat_helper(Glue, X, Y, Z) :- format(atom(Z), '~p~p~p', [X, Glue, Y]).

mapconcat(List, Glue, Result) :-
    reduce(List, mapconcat_helper(Glue), Result).

select_and_remove([], []).
select_and_remove(Elements, [E | Rest]) :-
    select(E, Elements, Elements0),
    select_and_remove(Elements0, Rest).

is_prefix([], _).
is_prefix(_, []) :- fail.
is_prefix([X | Xs], [X | Ys]) :- is_prefix(Xs, Ys).

is_sublist([], _).
is_sublist(_, []) :- fail.
is_sublist(Xs, [Y | Ys]) :- is_prefix(Xs, [Y | Ys]) ; is_sublist(Xs, Ys).

not_allowed([a, a, a]).
not_allowed([b, b]).
not_allowed([c, c]).
not_allowed([d, d]).

contains_not_allowed(P) :- not_allowed(Sub), is_sublist(Sub, P).

sans_repetitions(Result) :-
    findall(X, permutation([a, a, a, b, b, c, c, d, d], X), X),
    list_to_set(X, Y),
    exclude(contains_not_allowed, Y, Excluded), 
    length(Excluded, Result).

feed(Steaks, S, Kebabs, K) :-
    Steaks in 0..S, Kebabs in 0..K,
    indomain(Steaks), indomain(Kebabs),
    Total is Steaks + Kebabs,
    Total > 0.

feed_four([(S, K), (S1, K1), (S2, K2), (S3, K3)]) :-
    feed(S, 8, K, 10),
    Sr is 8 - S, Kr is 10 - K,
    feed(S1, Sr, K1, Kr),
    Sr1 is Sr - S1, Kr1 is Kr - K1,
    feed(S2, Sr1, K2, Kr1),
    S3 is Sr1 - S2, K3 is Kr1 - K2.

feed_families([(S, K), (S1, K1), (S2, K2), (S3, K3)]) :-
    Steaks = [S, S1, S2, S3],
    Kebabs = [K, K1, K2, K3],
    Steaks ins 0..8, sum(Steaks, #=, 8),
    Kebabs ins 0..10, sum(Kebabs, #=, 10),
    append([Steaks, Kebabs], Meals),
    maplist(indomain, Meals),
    SK is S + K, SK1 is S1 + K1, SK2 is S2 + K2, SK3 is S3 + K3,
    SK > 0, SK1 > 0, SK2 > 0, SK3 > 0.

barbecue :-
    findall(X, feed_families(X), X),
    length(X, N), 
    format('$$~p, ~p$$', [N]).

extra(Mask, Elt):- \+ member(Elt, Mask).

barbecue_1(Result) :-
    findall(X, feed_four(X), X),
    findall(Y, feed_families(Y), Y),
    include(extra(Y), X, Result).

%% bs --> [].
%% bs --> [b], as.
%% as --> [].
%% as --> [a], bs.

%% abs --> [].
%% abs --> [a], bs.
%% abs --> [b], as.

prefix_allowed(Sofar) :-
    not_allowed(Bad), is_prefix(Bad, Sofar).

valid_seqence(X, [], X).
valid_seqence(Sofar, Pool, Result) :-
    select(E, Pool, Rem), Next = [E | Sofar],
    \+prefix_allowed(Next),
    valid_seqence(Next, Rem, Result).
valid_seqence(X) :-
    valid_seqence([], [a, a, a, b, b, c, c, d, d], X).

sans_repetitions_2(Result) :-
    findall(X, valid_seqence(X), X),
    list_to_set(X, Y),
    length(Y, Result).
