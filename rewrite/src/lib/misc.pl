/* This module contains various utility predicates */

:- module(misc, [
		 fresh_pred_sym/1,
		 get_pairs/2,
		 get_ord_pairs/2,
		 substitute_term/4,
		 substitute_term_avl/4,
		 format_atom/3,
		 copy_instantiate/4,
		 negate/2, bb_inc/1,
		 reset_pred_sym/0
		], [hidden(true)]).
:- use_module(library(codesio)).
:- use_module(library(ordsets)).
:- use_module(library(terms)).
:- use_module(library(avl)).

bb_inc(Key) :-
	bb_get(user:Key, I),
	I1 is I+1,
        bb_put(user:Key, I1).

/* Copy T and instantiate Q to V in the new term */
copy_instantiate(T, Q, V, T1) :-
	term_variables_set(T, TVars),
	term_variables_set(Q, QVars),
	ord_subtract(TVars, QVars, FVars),
	copy_term(T-FVars-Q, T1-FVars-V).

/* T1=T[X1/X] : T1 is the result of replacing each occurrence of X in T by X1. */
substitute_term(X1, X, T, T1) :-
	(   T==X ->
	    T1=X1
	;   compound(T) -> 
	    functor(T, Sym, Arity)->
	    functor(T1, Sym, Arity),
	    (   foreacharg(TI, T),
		foreacharg(T1I, T1),
		param([X,X1])
	    do  substitute_term(X1, X, TI, T1I)
	    )
	;   T1=T
	).

/* AVL1:=AVL[X1/X]. Rebuilds AVL since subtituting might result in an unbalanced tree. */
substitute_term_avl(X1, X, AVL, AVL1) :-
	avl_to_list(AVL, L),
	substitute_term(X1, X, L, L1),
	list_to_avl(L1, AVL1).

get_pairs([], []).
get_pairs([S|Set], Pairs) :-
	(   foreach(S1, Set),
	    foreach((S-S1), SPairs),
	    param(S)
	do  true
	),
	get_pairs(Set, RecPairs),
	append(SPairs, RecPairs, Pairs).

get_ord_pairs(Set, Pairs) :-
	ord_setproduct(Set, Set, Product),
	(   foreach(S, Set),
	    foreach(S-S, Diag)
	do  true
	),
	ord_subtract(Product, Diag, Pairs).

reset_pred_sym :-
	bb_put(sym_num, 0).

fresh_pred_sym(Sym) :-
	(  bb_get(sym_num, N) ->
	    true
	;  N=0
	),
	N1 is N+1,
	bb_put(sym_num, N1),
	atom_codes(c, Prefix),
	number_codes(N, NumCodes),
	append(Prefix, NumCodes, Codes),
	atom_codes(Sym, Codes).

format_atom(Format, Arguments, Atom) :-
	format_to_codes(Format, Arguments, Codes),
	atom_codes(Atom, Codes).

/*LIA terms: negation */

% Negating A

negate(A=B, A=\=B).
negate(A==B, A\==B).
negate(A\==B, A==B).
negate(A=\=B, A=B).