/*
 * **********************************************
 * Printing result depth
 *
 * You can enlarge it, if needed.
 * **********************************************
 */
maximum_printing_depth(100).

:- current_prolog_flag(toplevel_print_options, A),
   (select(max_depth(_), A, B), ! ; A = B),
   maximum_printing_depth(MPD),
   set_prolog_flag(toplevel_print_options, [max_depth(MPD)|B]).

% Signature: unique(List, UniqueList, Dups)/3
% Purpose: succeeds if and only if UniqueList contains the same elements of List without duplicates (according to their order in List), and Dups contains the duplicates


unique([],[],[]).
unique([H | T], [H | X], Y) :- not_member(H,T),unique(T,X,Y).
unique([H | T], X, [H | Y] ) :- unique(T,X,Y),member(H,X).

member(X, [X|_Xs]).
member(X, [_Y|Ys]) :- member(X, Ys).

not_member(_, []).
not_member(X, [Head | Tail]) :- X \= Head, not_member(X, Tail).

