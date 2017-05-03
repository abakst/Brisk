:- module(tags, [
		 fresh_pred_sym/1,
		 tag_recvs/3,
		 check_tags/1,
		 tag_term/2,
		 get_proc/2,
		 sym_set/1,
		 check_race_freedom/2,
                 check_race_freedom_debug/2,
		 is_recv_from/1,
		 tags_independent/2,
		 parse_send/6,
		 parse_recv/6
		 ], [hidden(false)]).

:- use_module(library(ordsets)).
:- use_module(library(avl)).
:- use_module(library(terms)).
:- use_module('lib/misc.pl', [ fresh_pred_sym/1]).

/*
tag(a, t): action a has tag t.
*/

:- dynamic tags/2,   /* tags(P-Q, Tags): sends with tags
	                Tags were sent on channel P-Q.
		     */
	proc/1,       /* proc(P): P is a process in the current universe. */
	proc/2,      /* proc(Tag, Proc): Tag "Tag" belongs to process p. */
	talksto/2,   /* talksto(P,Q)   : Q can receive messages from P */
	type/2,      /* type(Tag, Type): Tag "Tag" belongs to a send of type "Type".  */
	sym_set/1.   /* sym_set(S): S is a set of symmetric processes. */

cleanup :-
	retractall(tags(_,_)),
	retractall(proc(_)),
	retractall(proc(_,_)),
	retractall(talksto(_,_)),
	retractall(type(_,_)),
	retractall(sym_set(_)).


is_recv_from(T) :-
  /*
	Check that T is a receive from a specific process.
  */
  (   functor(T, recv, 3)
  ;   functor(T, recv, 4)
  ),
  arg(2, T, Exp),
  functor(Exp, F, _),
  (   F==e_var
  ;   F==e_pid
  ).

parse_send(T, Rho, P, Q, Type, V) :-
	/*
	send(p, q, type, v): p sends a message v of type "type" to process q.
	*/
	(   functor(T, send, 3) ->
	    T=send(P, Exp, V)
	;   functor(T, send, 4) ->
	    T=send(P, Exp, Type, V)
	),
	parse_pid_exp(Exp, P, Rho, Q).


parse_recv(T, Rho, P, Q, Type, V) :-
	/*
	recv(p, q, type, v): p receives a message v of type "type" from process q.
	*/
	(   (   functor(T, recv, 2)->
		T=recv(P, V)
	    ;	functor(T, recv, 3)->
		T=recv(P, Exp, V),
		(   Exp=type(Type) ->
		    true
		;   PidExp=Exp
		)
	    ;   functor(T, recv, 4) ->
		T=recv(P, PidExp, Type, V)
	    ),
%	    atomic(P),
	    (   nonvar(PidExp) ->
		parse_pid_exp(PidExp, P, Rho, Q0),
		(		%false,user:symset(Q, Q0)
		    user:is_valid(fresh(Q1)),
		    user:is_valid(element(Q1, Q0)),
		    Q=Q1
		;   Q=Q0
		)
	    ;   true
	    )
	).

parse_pid_exp(PidExp, P, Rho, Q) :-
	/*
	If PidExp is of the form e_pid(q), return q.
	If PidExp is of the form e_var(x) return rho(p, x).
        Throws an exception otherwise.
	*/
	(   functor(PidExp, e_pid, 1) ->
	    arg(1, PidExp, Q)
	;   functor(PidExp, e_var, 1) ->
	    arg(1, PidExp, X),
	    (   is_avl(Rho)->
		avl_fetch(P-X, Rho, Q)
	    ;   true
	    )
	;   throw(parse-pid-error(PidExp))
	).

tag_sends(T, Proc, T1) :-
/*
Recursively traverses T and transforms each send S into tag(S, Tag), where Tag is a fresh constant. While tagging, it updates the data-structures described in the dynamic predicates above. Proc either contains var(P, S) to indicate that variable P is bound to a process in set S, or none otherwise.
*/
	(   simple(T) ->
	    T1=T
	;   parse_send(T, _, P, Q, Type, _) ->	
	    fresh_pred_sym(Tag),
	    (   nonvar(Type)->
		assert(type(Tag, Type))
	    ;   true
	    ),
	    sub_sym_set(P, Proc, P1),
	    sub_sym_set(Q, Proc, Q1),
	    assert(proc(Tag, P1)),
	    assert(tags(P1-Q1, Tag)),
	    T1=tag(T, Tag)
	;   functor(T, sym, 3) ->
	    T=sym(P, S, A),
	    assert(sym_set(S)),
	    tag_sends(A, var(P, S), A1),
	    T1=sym(P, S, A1)
	;   functor(T, for, 4) ->
	    T=for(M, P, S, A),
	    assert(sym_set(S)),
	    tag_sends(A, var(P, S), A1),
	    T1=for(M, P, S, A1)
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1),
		param(Proc)
	    do  tag_sends(Arg, Proc, Arg1)
	    )
	).
tag_recvs(T, Proc, T1) :-
/*
Tag each receive with all tags on the appropriate channel.
*/
	(   simple(T) ->
	    T1=T
	;   functor(T, recv, 2) ->
	    T=recv(P, _),
	    sub_sym_set(P, Proc, P1),
	    findall(Tag, (tags(Q-P1,Tag), Q\=P1), Tags),
	    set_talksto(P1, Tags),
	    T1=tag(T, Tags)
	;   (   functor(T, recv, 3) ->
		T=recv(P, X, _)
	    ;   functor(T, recv, 4) ->
		T=recv(P, X, Type, _)
	    ),
	    sub_sym_set(P, Proc, P1),
	    (   X=e_pid(Q) ->
		true
	    ;   X=e_var(_) ->
		true
	    ;   X=type(Type) ->
		true
	    ;  throw(parse-pid-error(X))
	    ),
	    sub_sym_set(Q, Proc, Q1),
	    findall(Tag, (tags(Q1-P1,Tag), Q1\=P1, (nonvar(Type)->type(Tag, Type);true)), Tags)->
	    set_talksto(P1, Tags),
	    T1=tag(T, Tags)
	;   functor(T, sym, 3) ->
	    T=sym(P, S, A),
	    tag_recvs(A, var(P, S), A1),
	    T1=sym(P, S, A1)
	;   functor(T, for, 4) ->
	    T=for(M, P, S, A),
	    tag_recvs(A, var(P, S), A1),
	    T1=for(M, P, S, A1)
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1),
		param(Proc)
	    do  tag_recvs(Arg, Proc, Arg1)
	    )
	).

set_talksto(P, Tags) :-
	(   foreach(Tag, Tags),
	    param(P)
	do  (   proc(Tag, Q),
		P\==Q->
		assert(talksto(P,Q))
	    ;   true
	    )
	).

check_tags(T) :-
/*
Checks if all receive tag-sets either
 a)  consist of a single tag or
 b)  constist of tags from the same process and that process is not symmetric.
*/
	(   simple(T) ->
	    true
	;   functor(T, tag, 2),
	    T=tag(Rec, Tags),
	    functor(Rec, recv, _) ->
	    (   Tags=[Tag]->
		true
	    ;   is_recv_from(Rec) ->
		true
	    ;   (   foreach(Tag, Tags),
		    param(Proc, T)
		do  proc(Tag, Proc),
		    \+sym_set(Proc) ->
		    true
		;   throw(race-condition(T))
		)
	    )
	;   (   foreacharg(Arg, T)
	    do  check_tags(Arg)->
		true
	    )
	).

untag_add_receive_from(T, T1) :-
/*
Takes a tagged term, removes tags and plugs in receive-from information.
*/

	(   simple(T) ->
	    T1=T
	;   functor(T, tag, 2),
	    T=tag(Send, Tag),
	    functor(Send, send, _) ->
	    T1=Send
	;   functor(T, tag, 2),
	    T=tag(Recv, Tags),
	    functor(Recv, recv, _) ->
	    (   Tags=[Tag|_]->
		proc(Tag, Q),
		(   Recv=recv(P, V)->
		    T1=recv(P, e_pid(Q), V)
		;   Recv=recv(P, type(Type), V) ->
		    T1= recv(P, e_pid(Q), Type, V)
		;   T1=Recv
		)
	    ;   T1=Recv
	    )
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1)
	    do untag_add_receive_from(Arg, Arg1)
	    )
	).


sub_sym_set(P, Proc, P1) :-
	/*
	If P belongs to a symmetric set S, then P1=S, and P1=P, otherwise.
	*/
	(   Proc=var(Q, S),
	    Q==P->
	    P1=S
	;   P1=P
	).

assert_procs(T) :-
	(   simple(T) ->
	    true
	;   get_proc(T, P),
	    assert(proc(P))
	;   functor(T, nondet, _)
	;   (   foreacharg(Arg, T)
	    do  assert_procs(Arg)
	    )
	).

get_proc(T, P) :-
	/*Recursively traverse T and assert proc(P), if process P performs an action.*/
	(   functor(T, F, _),
	    ord_member(F, [assign,if,ite,iter,recv,send,while])->
	    arg(1, T, P)
	;   functor(T, for, 4)->
	    arg(1, T, P)
	;   functor(T, sym, 3),
	    arg(2, T, P)
	).


tags_independent(P, Q) :-
/* Two processes P and are independent iff
	no sends happen along the channel P-Q. */
	proc(P),
	proc(Q),
	P\==Q,
	\+talksto(P,Q),
	\+talksto(Q,P).

tag_term(T, T2)	:-
	cleanup,
	assert_procs(T),
	tag_sends(T, none, T1),
	tag_recvs(T1, none, T2).

check_race_freedom(T, T2) :-
	tag_term(T, T1),
/*	portray_clause(T1), */
	check_tags(T1),
	untag_add_receive_from(T1, T2).

check_race_freedom_debug(T,T2) :-
        catch( check_race_freedom(T,T2)
             , race-condition(X)
             , T2=race(X)
             ).
