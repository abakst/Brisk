:- use_module(library(avl)).
:- use_module(library(lists)).
:- use_module(library(terms)).
:- use_module(library(ordsets)).
:- use_module('lib/misc.pl', [ format_atom/3, fresh_pred_sym/1,
			       substitute_term/4,substitute_term_avl/4,
			       copy_instantiate/4,get_ord_pairs/2,
			       get_pairs/2,
			       negate/2, bb_inc/1,
			       reset_pred_sym/0
			     ]
	     ).

:- use_module('tags.pl', [
			  check_race_freedom/2,
			  tags_independent/2,
			  get_proc/2,
			  is_recv_from/1,
			  parse_send/6,
			  sym_set/1,
			  parse_recv/6
			 ]).

:- dynamic independent/2, /* independent(p,q): processes p and q are independent.*/
	   talkto/2,      /* talkto(p,q): p and q are communicating, all other procs are external. */
	   symset/2,      /* symset(p, S): process p belongs to the set of symmetric processes S. */
	   in_remove/0,
	   asserted/1,    /* asserted(cons): cons is valid. */
     in_for/0,
	   max_delta/3.   /*
	                     max_delta(Max, T, Delta): max is the length of delta,
	                     the longest prefix that occurred in any rewrite-step so far.
			  */
	   

/*==============================================================================
 Language:
================================================================================

Core languange:
---------------
 par([A,B,C])        : A || B || C.
 seq([A,B,C])        : A; B; C.
 skip                : no-operation.
 send(p, x, v)       : process p sends value v to
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
send(p, x, type, v)  : send a message of type "type".
 recv(p, v)          : process p receives value v.
 recv(p, x, v)       : process p receives value v from
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
  | x=type(t)        :       - of type t.
 recv(p, x, type, v) : receive messages of type "type", only.
 sym(P, S, A)        : composition of symmetric processes p in set s with source A.
                       s must be distinct from process ids.
 for(m, P, S, A)     : process m executes A for each process p in s.
 iter(p, k, A)       : process p executes A k-times.
 while(p, cond, A)   : process p executes A while cond is true.
 nondet(P, s, A)        : process P is chosen non-deterministically in A.
 assign(p, x, v)     : process p assigns value v to variable x.
 ite(P, Cond, A, B)  : process p executes A if Cond holds and B, otherwise.
 if(P, Cond, A)      : Short for ite(P, Cond, A, skip).
 pair(x, y)          : pair of values x and y.
 cases(p, x, C, d)   : proccess p performs a case switch on x with cases specified in
 | C=case(p, exp, A) : C and default case d.

(Set) constraints:
------------------
 fresh(p)            : p is fresh.
 emp                 : ∅.
 setOf([a,b,...])    : {a,b,...}.
 element(p, S)       : p in S.
 subset(P, Q)        : P ⊆ Q.
 prop_subset(P, Q)   : P ⊂ Q.
 set_minus(P, Q)     : P\{Q}.
 assume(cons)        : assume cons holds.

Terms are expected to be of the form par([ seq([..,]), ...]).
==============================================================================
==============================================================================*/

/*===================================
 TODOs:
   - conditionals: variables vs constants.
   - recv(p, q, type, v) as primitive, derive others
   - same for send.
   - Fix nondet.
   - check rho assignments.
===================================*/

replace_proc_id(Proc1, Proc, Rho, Rho1) :-
	/*
	Transform all constant assignments for process Proc into mappings for process Proc1.
	*/
	findall(Proc-Var-Val, avl_member(Proc-Var, Rho, Val), L),
	  (   foreach(Proc-Var-Val, L),
	      fromto(Rho, RhoIn, RhoOut, Rho1),
	      param(Proc1)
	  do  avl_delete(Proc-Var, RhoIn, _, RhoIn1),
	      substitute_term(Proc1, Proc, Val, Val1),
	      avl_store(Proc1-Var, RhoIn1, Val1, RhoOut)
	  ).

add_external(Psi, T, P, Psi1) :-
	(  avl_fetch(P, Psi, L)
	;  L=[]
	),
	append(L, [T], L1),
	avl_store(P, Psi, L1, Psi1).


rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) :-
	/*
	       T:    Process term.
	   Gamma:    Environment containing message buffer for each process pair.
	   Delta:    Prefix of rewritten communication.
	     Rho:    Map from variables to constants.
             Psi:    Remainder term given as map from process to list of actions.
	*/
	(
	  cleanup_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)->
	  true
	/*
	while(p, cond, A): remove after one iteration --bit hacky
	*/
	; functor(T, while, 3),
	T= while(P, Cond, A),
	check_cond(Cond, P, Rho),
	rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma2, Delta2, Rho2, Psi),
	negate(Cond, NegCond),
	check_cond(NegCond, P, Rho2)->
	T1=skip,
	Gamma1=Gamma2,
	Delta1=Delta2,
	Rho1=Rho2,
	Psi1=Psi

	/*
	/*****************************************
	recv: receive if there's a pending message.
	*****************************************/
	; parse_recv(T, Rho, P, Q, Type, X),
	  avl_member(Q-P, Gamma, [V-Type|Vs]) ->
	  T1=skip,
	  append(Delta, [assign(P, X, V)], Delta1),
	  (   Vs==[] ->
	      avl_delete(Q-P, Gamma, _, Gamma1)
	  ;   avl_store(Q-P, Gamma, Vs, Gamma1)
	  ),
	  (   /****************************************
	  propagate constant from assignment in Q.
	  ****************************************/
	      propagate_const(Q, V, Rho, V1)
	  ;   V1=V
	  ),
	  update_constants(P, X, V1, Rho, Rho1),
	  Psi=Psi1
	/*
	if(P, Cond, A): syntactic sugar for ite(P, Cond, A, skip).
	*/
	; functor(T, if, 3),
	  T=if(P, Cond, A)->
	  T1=ite(P, Cond, A, skip),
	  Gamma1=Gamma, Delta1=Delta,
	  Rho1=Rho, Psi1=Psi
	/*
	ite(P, Cond, A, B): reduce to A, if Cond holds and B, if not Cond holds.
	*/
	; functor(T, ite, 4),
	  T = ite(P, Cond, A, B),
	  (   check_cond(Cond, P, Rho) ->
	      T1=A
	  ;   negate(Cond, NegCond),
	      check_cond(NegCond, P, Rho) ->
	      T1=B
	  )->
	  Gamma1=Gamma, Delta1=Delta,
	  Rho1=Rho, Psi1=Psi
	/*
	par([A,B,C,...])
	*/
	; functor(T, par, 1) ->
	  arg(1, T, L),
	  list_to_ord_set(L, OL),
	  (   OL==[] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   OL = [A] ->
	      T1=A, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   select(A, OL, LR),
	      (   A==skip->
		  T1=par(LR), Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      )
	  /*
	  rewrite ordered pairs of expressions
	  */
	  ;   get_ord_pairs(OL, Pairs),
	      select(TL-TR, Pairs, _),
	      rewrite_step(par(TL, TR), Gamma, Delta, Rho, Psi, T2, Gamma1, Delta1, Rho1, Psi1)->
	      list_to_ord_set([TL,TR], Ts),
	      ord_subtract(OL, Ts, Ts1),
	      unpack_par(T2, T2L),
	      append([T2L,Ts1], L2),
	      T1=par(L2)
	  )
	  /*
	  seq([A|B])
	  */
	; functor(T, seq, 1) ->
	  arg(1, T, L),
	  (   L == [] ->
	      T1=skip, Gamma1=Gamma, Delta1=seq(Delta), Rho1=Rho, Psi=Psi1
	  ;   L = [A] ->
	      T1=A, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   L=[A|B],
	      (  A==skip ->
		  T1=seq(B),Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1) ->
		  T1=seq([A1|B])
	      )
	  )


	/**********************
	        Unfolding
	**********************/

	/*
	================
	for-loop
	================
	p* fresh
	s* fresh
	∅ ⊂ s* ⊆ s and p*∈s*
	par(A(p*), sym(Q, s*, B)) ~~>
	par(skip, par(sym(P, s*\p1, B), C(p1)))
	---------------------------------------
	par(for(m, P, s, A), sym(Q, s, B)) ~~>
	par(skip, sym(Q, s, C))
	*/
	; functor(T, par, 2),
	  arg(1, T, For),
	  functor(For, for, 4),
	  For=for(M, P, S, A),
	  arg(2, T, Sym),
	  Sym=sym(Q, S, B),
%	  fresh_pred_sym(Proc),
	  make_instance(Proc),
	  %fresh_pred_sym(S1),
	  make_instance(S1),
	  assert(symset(Proc, S)),
	  copy_instantiate(A, P, Proc, A1),
	  assert(asserted(prop_subset(emp, S1))),
	  assert(asserted(subset(S1, S))),
	  assert(asserted(element(Proc, S1))),
	  substitute_term(Proc, P, Rho, Rho2),
	  mk_pair(A1, sym(Q, S1, B), TA, Switched),
	  mk_pair(skip, par(sym(Q, set_minus(S1, Proc1), B), C), TB, Switched),
	  assert(in_for),
	  (   rewrite(TA, Gamma, [], Rho2, Psi, TB, Gamma, Delta2, Rho3, Psi2)
	  ;   retractall(in_for),
	      fail
	  )->
	  retractall(in_for),
	  clear_talkto,
	  substitute_term(Q, Proc1, C, C1),
          replace_proc_id(S, Proc1, Rho3, Rho4),
	  substitute_term(P, Proc, Rho4, Rho5),
	  substitute_term(S, Proc1, Rho5, Rho1),
	  mk_pair(skip, sym(Q,S,C1), T1, Switched),
	  Gamma1=Gamma,
          substitute_term(P, Proc1, Delta2, Delta3),
	  append(Delta, [for(P, S ,Delta3)], Delta1),
          (   avl_delete(Proc1, Psi2, Ext0, Psi3) ->
	      substitute_term(Q, Proc1, Ext0, Ext),
	      add_external(Psi3, sym(Q, S, seq(Ext)), S, Psi1)
	  ;   Psi1=Psi
	  )

	/*
	================
	iter-repeat
	================
        par(A, B) ~~>
        par(skip, B)
	---------------------------------------
        par(iter(m,k, A), B) ~~>
        par(skip, B)
	*/

        ; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, B),
	  functor(TA, iter, 3),
	  TA = iter(M, K, A),
          empty_avl(Psi),
          rewrite(par(A, B), Gamma, [], Rho, Psi, par(skip, B), Gamma, Delta2, _, Psi2)->
          clear_talkto,
          T1 = par(skip, B),
          Gamma1=Gamma,
          get_proc(B, Proc),
          append(Delta, [iter(Proc, K , Delta2)], Delta1),
          Rho1=Rho,
          (   avl_delete(Proc, Psi2, Ext, Psi3) ->
              add_external(Psi3, iter(Proc, K, seq(Ext)), Proc, Psi1)
	  ;   Psi1=Psi
	  )
	/* Rewrite cases in context. Syntax reminder:
	cases(p, x, C, d)   : proccess p performs a case switch on x with cases specified in
	| C=case(p, exp, A) : C and default case d.
	*/
	; functor(T, par, 2),
	  mk_pair(TA, D, T, Switched),
	  normalize_seq(TA, TA1),
	  (   functor(TA1, seq, 1)->
	      TA1=seq([Cases|C]),
	      functor(Cases, cases, 4),
	      Cases=cases(P, X, Cs, skip)
	  ;   functor(TA1, cases, 4),
	      TA1=cases(P, X, Cs, skip),
	      C=[]
	  ),
          \+match_case(P, X, Cs, Rho, _, _),
          atomic(X),
	  empty_avl(Psi),
          (   foreach(case(P, Exp, A), Cs),
	      foreach(case(P, Exp, CDelta), CDeltas),
	      fromto(full_avl, In, Out, Rho1),
	      param([X,D,C,Gamma,Rho,Psi,Gamma2, Switched, Pair1])
	  do  T2=seq([assign(P,X,Exp),A|C]),
	      mk_pair(T2, D, Pair, Switched),
	      /* rewrite one component to skip */
	      contains_skip(Pair1),
	      rewrite(Pair, Gamma, [], Rho, empty, Pair1, Gamma2, CDelta, Rho2, Psi2),
	      (   empty_avl(Psi2)->
		  true
	      ;   Psi2=Psi1
	      ),
	      intersect_avl(In, Rho2, Out)
	  )->
	  (   var(Psi1)->
	      empty_avl(Psi1)
	  ;   true
	  ),
          append(Delta, [cases(P, X, CDeltas)], Delta1),
	  Gamma1=Gamma2,
	  T1=Pair1
%	  Psi1=Psi
	/*
	================
	sym-repeat
 	================
        p* fresh
        par(sym(P, s, A), B) ~~>
        par(par(sym(P, s\{q}, A), A(q)), skip)
	---------------------------------------
        par(sym(P, s, A), B) ~~>
        sym(P, s, A)
        */
        ; functor(T, par, 2),
	  mk_pair(B, TA, T, Switched),
	  functor(TA, sym, 3),
	  TA=sym(P, S, A),
	  TA1=par(sym(P, set_minus(S, Proc), A), AProc),
	  mk_pair(skip, TA1, T2, Switched),
	  \+in_remove,
	  \+in_for,
	  assert(in_remove),
	  ( %rewrite(par(B, TA), Gamma, [], Rho, Psi, par(skip, TA1), Gamma, Delta2, Rho2, Psi2)
	      rewrite(T, Gamma, [], Rho, Psi, T2, Gamma, Delta2, Rho2, Psi2)
	  ;   retractall(in_remove),
	      fail
	  ),
	  substitute_term(Proc, P, A, AProc),
%	  substitute_term(Proc, P, A, A1),
%	  rewrite(A1, AProc, DeltaInt, _) ->
	  retractall(in_remove),
	  clear_talkto,
	  mk_pair(skip, sym(P, S, A), T1, Switched),
%	  T1=par(skip, sym(P, S, A)),
	  Gamma1=Gamma,
	  Rho1=Rho,
	  substitute_term(Fresh1, Proc, Delta2, Delta3),
	  append(Delta, [nondet(Fresh1, S, seq(Delta3))], Delta1),
	  (   avl_delete(Proc, Psi2, Ext0, Psi3) ->
	      substitute_term(Fresh2, Proc, Ext0, Ext),
	      add_external(Psi3, nondet(Fresh2, S, seq(Ext)), S, Psi1),
	      assert(symset(Fresh2, S))
	  ;   Psi1=Psi
	  )
	/*
	=============
	unfold-send:
	=============
	p ∈ P
	---------
	par([send(_, p, _), sym(Q, s, A)]) ~~>
	par([send(_, p, _, _), sym(Q, set_minus(s, p), A(Q)), A(p)])
	*/
	; functor(T, par, 2),
	  mk_pair(Send, Sym, T, Switched),
	  parse_send(Send, Rho, M, P, _, _),
%	  arg(1, T, Send),
%	  parse_send(Send, Rho, M, P, _, _),
%	  arg(2, T, Sym),
	  functor(Sym, sym, 3),
	  Sym=sym(Q, S, A),
	  nonvar(P),
	  is_valid(element(P, S))->
	  assert(symset(P, S)),
	  copy_instantiate(A, Q, P, AP),
	  set_talkto(M, P),
	  Sym1=par(sym(Q, set_minus(S,P), A), AP),
	  mk_pair(Send, Sym1, T1, Switched),
%	  T1=par(Send, Sym1),
	  replace_proc_id(P, S, Rho, Rho2),
	  /* Instantiate assignments for all supersets. */
	  (   findall(S1, (is_valid(subset(S, S1)),S\==S1), Subsets)->
	      (   foreach(S1, Subsets),
		  fromto(Rho2, In, Out, Rho1),
		  param([P,S])
	      do  replace_proc_id(P, S1, In, Out)
	      )
	  ;   true
	  ),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Psi1=Psi
	/*
	=============
	unfold-recv:
	=============
	 p* fresh
	 ∅ ⊂ s1 ⊆ s
	---------------------------------------
	par([recv(_, s, _), sym(Q, s1, A)]) ~~>
	par([recv(_, p*, _, _), sym(Q, set_minus(s1, p*), A(Q)), A(p*)])
	*/
	; functor(T, par, 2),
	  T=par(Recv, Sym), %mk_pair(Recv, Sym, T, Switched),
	  is_recv_from(Recv),
	  parse_recv(Recv, Rho, P, S, Type, V),
	  arg(2, T, Sym),
	  functor(Sym, sym, 3),
	  Sym=sym(Q, S1, A),
	  nonvar(S),
	  is_valid(prop_subset(emp, S1)),
	  is_valid(subset(S1,S))->
	  make_instance(Proc),
%	  fresh_pred_sym(Proc),
          is_valid(subset(S1,S)),
	  set_talkto(P, Proc),
	  assert(symset(Proc, S1)),
	  assert(asserted(element(Proc, S1))),
	  copy_instantiate(A, Q, Proc, AP),
	  Sym1=par(sym(Q, set_minus(S1, Proc), A), AP),
	  Recv1=recv(P, e_pid(Proc), Type, V),
          T1=par(Recv1, Sym1),
%	  mk_pair(Recv1, Sym1, T1, Switched),
	  replace_proc_id(Proc, S, Rho, Rho1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Psi1=Psi

	/**********************
	        Loops
	**********************/
	/*

	/*
	================
	sym-remove
	================
        C<B
        par(sym(P, s, B), A) ~~>
        par(par(sym(P, s\{p1}, B), C(p1)), A)
	---------------------------------------
        par(sym(P, s, B), A) ~~>
        par(sym(P, s, C), A)
        */

        ;  functor(T, par, 2),
           %mk_pair(TB, A, T, Switched),
           %functor(T, par, 2),
           arg(1, T, TB),
	   arg(2, T, A),
           functor(TB, sym, 3),
           TB=sym(P, S, B),
           TB1=par(sym(P, set_minus(S, Proc1), B), C),
%           mk_pair(TB1, A, T2, Switched),
           T2=par(TB1, A),
           \+in_remove,
           \+in_for,
	  assert(in_remove),
           (   rewrite(T, Gamma, [], Rho, Psi, T2, Gamma, Delta2, Rho2, Psi2)
           ;   retractall(in_remove),
	       fail
	   ),
           retractall(in_remove),
%           rewrite(A1, A, _, _),
           substitute_term(P, Proc1, C, C1),
           smaller_than(C1, B) ->
           clear_talkto,
           replace_proc_id(S, Proc1, Rho2, Rho1),
           mk_pair(sym(P, S, C1), A, T1, Switched),
%           T1=par(sym(P, S, C1), A),
           Gamma1=Gamma,
           substitute_term(P, Proc1, Delta2, Delta3),
           append(Delta, [for(P, S ,Delta3)], Delta1),
           (   avl_delete(Proc1, Psi2, Ext0, Psi3) ->
	       substitute_term(P, Proc1, Ext0, Ext),
	       add_external(Psi3, sym(P, S, seq(Ext)), S, Psi1)
	   ;   get_proc(A, M),
	       avl_delete(M, Psi2, Ext0, Psi3) ->
	       substitute_term(P, Proc1, Ext0, Ext),
	       add_external(Psi3, iter(M, S, seq(Ext)), M, Psi1)
	   ;   Psi1=Psi
	   )

	/*
	for(M, P, S, A): reduce A.
	*/
	; functor(T, for, 4),
	  T=for(M, P, S, A),
	  make_instance(Proc),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  copy_instantiate(A, P, Proc, A1),
	  assert(symset(Proc, S)),
	  assert(asserted(element(Proc, S))),
	  empty_avl(Emp),
	  rewrite(A1, Gamma, [], Rho2, Emp, skip, Gamma, Delta2, Rho3, PsiA) ->
	  substitute_term(P, Proc, B, B1),
	  T1=skip,
	  replace_proc_id(S, Proc, Rho3, Rho4),
	  substitute_term(P, Proc, Rho4, Rho1),
	  Gamma1=Gamma,
	  (   Delta2 == [] ->
	      Delta1=Delta
	  ;   substitute_term(P, Proc, Delta2, Delta3),
	      append(Delta, [for(P, S ,Delta3)], Delta1)
	  ),
	  (   avl_delete(M, PsiA, Ext0, _) ->
	      substitute_term(P, Proc, Ext0, Ext),
	      add_external(Psi, for(M, P, S, seq(Ext)), M, Psi1)
	  ;   Psi1=Psi
	  )
	/*
	Reduce cases
	*/
	; functor(T, cases, 4),
	  T=cases(P, X, Cs, skip),
	  (   foreach(case(P, Exp, A), Cs),
	      foreach([assign(P, X, Exp)|Delta2], Deltas),
	      fromto(full_avl, In, Out, Rho1),
	      param([T,P,X,Gamma,Delta,Rho,Psi])
	  do rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma, Delta2, Rho2, Psi)->
	      intersect_avl(In, Rho2, Out)
	  )->
	  append(Delta, [cases(P, X, Deltas)], Delta1),
	  T1=skip,
	  Gamma1=Gamma, 
	  Psi1=Psi

	/*
	send(p, x, v)
	*/
	; parse_send(T, Rho, P, Q, Type, V),
	  (   avl_fetch(P-Q, Gamma, Vs)
	  ;   Vs=[]
	  ),

%	  substitute_constants(V, P, Rho, V1),
	  append(Vs, [V-Type], Vs1),
	  avl_store(P-Q, Gamma, Vs1, Gamma1),
	  T1=skip,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi=Psi1
        /*
	par(iter(p, k, A), iter(q, k, B) ): merge two iter loops.
	*/
	; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, TB),
	  functor(TA, iter, 3),
	  functor(TB, iter, 3),
	  TA = iter(_, K, A),
	  TB = iter(_, K, B),
	  empty_avl(Psi),
	  mk_pair(A, B, Pair),
	  rewrite(Pair, Gamma, [], Rho, Psi, par(skip, skip), Gamma, Delta2, _, Psi)->
	  T1=par(skip, skip),
	  Gamma1=Gamma, Rho1=Rho, Psi1=Psi,
	  append(Delta, [iter(env, K, seq(Delta2))], Delta1)
        /*
	par(A, while(P, Cond, B)): exit
	*/
	; functor(T, par, 2),
	  arg(1, T, A),
	  arg(2, T, TB),
	  functor(TB, while, 3),
          TB=while(P, Cond, B),
          check_cond(Cond, P, Rho),
          mk_pair(A, B, Pair, Switched),
          mk_pair(A1, skip, Pair1, Switched),
	  empty_avl(Psi),
	  rewrite(Pair, Gamma, [], Rho, Psi, Pair1, Gamma, Delta2, Rho1, Psi1),
          negate(Cond, NegCond),
          check_cond(NegCond, P, Rho1)->
	  T1=par(A1, skip),
	  append(Delta, [Delta2], Delta1),
          Gamma1=Gamma
	/*
	par(A, while(P, Cond, B)): continue
	*/
	; functor(T, par, 2),
	  arg(1, T, A),
	  arg(2, T, TB),
	  functor(TB, while, 3),
          TB=while(P, Cond, B),
          check_cond(Cond, P, Rho),
          mk_pair(A, B, Pair, Switched),
          mk_pair(A1, skip, Pair1, Switched),
	  empty_avl(Psi),
	  rewrite(Pair, Gamma, [], Rho, Psi, Pair1, Gamma, Delta2, Rho1, Psi1),
          check_cond(Cond, P, Rho1)->
	  T1=par(A1, TB),
	  append(Delta, [Delta2], Delta1),
          Gamma1=Gamma
	/*
	par(seq([ite(P, Cond, A, B), C]), D): reduce both par(A,C) and par(B, C) to skip.
	*/
	/*TODO: keep assignments in rho that are occur on both branches.*/
	; functor(T, par, 2),
	  T=par(TA, D),
	  (   functor(TA, seq, 1)->
	      TA=seq([ITE|C]),
	      functor(ITE, ite, 4),
	      ITE=ite(P, Cond, A, B)
	  ;   functor(TA, ite, 4) ->
	      TA=ite(P, Cond, A, B),
	      C=[]
	  ),
	  rewrite(par([seq([A|C]),D]), Gamma, [], Rho, Psi, skip, Gamma2, DeltaA, _, Psi),
	  rewrite(par([seq([B|C]),D]), Gamma, [], Rho, Psi, skip, Gamma2, DeltaB, _, Psi)->
	  append(Delta, [ite(Cond, seq(DeltaA), seq(DeltaB))], Delta1),
          empty_avl(Rho1),
	  Gamma1=Gamma2,
	  T1=par(skip, skip),
	  Psi1=Psi

	  /*
	  par(A, B): rewrite ordered pairs.
	  */
	; functor(T, par, 2) ->
	  arg(1, T, A),
	  arg(2, T, B),
          /* rewrite expanded sets */
          (   functor(B, par, 2),
	      B=par(Sym, C),
	      Sym=sym(_, Set, _),
              Set=set_minus(_,_),
	      mk_pair(A, C, Pair, Switched),
	      mk_pair(A1, C1, Pair1, Switched),
	      rewrite_step(Pair, Gamma, Delta, Rho, Psi, Pair1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A1, par(Sym, C1))
	  ;   functor(A, seq, 1),
	      (   cleanup_seq(A, A1)->
		  T2=par(A1, B),
		  rewrite_step(T2, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)
	      ;   A=seq([C|Cs]),
		  rewrite_step(par(C, B), Gamma, Delta, Rho, Psi, par(C1, B1), Gamma1, Delta1, Rho1, Psi1)->
		  T1=par(seq([C1|Cs]), B1)
	      )
	  ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A1, B)
	  ;   rewrite_step(B, Gamma, Delta, Rho, Psi, B1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A, B1)
	  )
	).

rewrite(T, Gamma, Delta, Rho, Psi, T2, Gamma2, Delta2, Rho2, Psi2) :-
	(   subsumed_by(T, T2),
	    Gamma=Gamma2, Delta=Delta2, Rho=Rho2, Psi= Psi2
	;   rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1)->
	    update_max_delta(T1, Delta1),
	    sanity_check([T1, Gamma1, Delta1, Rho1, Psi1]),
	    rewrite(T1, Gamma1, Delta1, Rho1, Psi1, T2, Gamma2, Delta2, Rho2, Psi2)
	).

cleanup_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) :-
	/*
	Remove constructs (such as assign/skip) that do not affect communication.
	*/
	(
	  /*
	  assign(p, x, v): p assigns v to x.
	  */
	  functor(T, assign, 3),
	  T=assign(P, X, V),
	  ground(P) ->
	  T1=skip,
	  append(Delta, [T], Delta1),
	  (   nonvar(V),
	      (   avl_member(P-V, Rho, V1)->
		  avl_store(P-X, Rho, V1, Rho1)
	      ;   avl_store(P-X, Rho, V, Rho1)
	      )
	  ;   throw(assing-to-var(assign(P, X, V)))
	  ),
	  Gamma1=Gamma,
	  Psi1=Psi
	/*
	external send/recv-from.
	*/
	; (   parse_send(T, Rho, P, Q, _, _)
	  ;   parse_recv(T, Rho, P, Q, _, _),
	      is_recv_from(T)
	  ),
	  talkto(P, M),
	  check_independent(Q, M)->
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  add_external(Psi, T, P, Psi1)
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  \+contains_var(P,A),
	  rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma, Delta1, Rho1, Psi) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Psi1=Psi	
	/*
	Case
	*/
	; functor(T, cases, 4),
	  T=cases(P, X, Cs, _),
	  match_case(P, X, Cs, Rho, Rho1, A) ->
	  T1=A,
	  Gamma1=Gamma, Delta1=Delta,
	  Psi1=Psi
	/*Reduce
	while(p, cond, A): remove while if cond doesn't hold.
	*/
	; functor(T, while, 3),
	  T= while(P, Cond, _),
	  negate(Cond, NegCond),
	  check_cond(NegCond, P, Rho) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/*
	sym(P, S, A): reduce A in sym(P, S, A)
	*/
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  empty_avl(Psi),
	  make_instance(Proc),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  copy_instantiate(A, P, Proc, A1),
	  cleanup_step(A1, Gamma, [], Rho2, Psi, B, Gamma, Delta2, Rho3, Psi) ->
	  substitute_term(P, Proc, B, B1),
	  T1=sym(P, S, B1),
	  replace_proc_id(S, Proc, Rho3, Rho4),
	  substitute_term(P, Proc, Rho4, Rho1),
	  Gamma1=Gamma,
	  (   Delta2 == [] ->
	      Delta1=Delta
	  ;   substitute_term(P, Proc, Delta2, Delta3),
	      append(Delta, [for(P, S ,Delta3)], Delta1)
	  ),
	  Psi1=Psi
	/*
	Process remainder term.
	*/
	; functor(T, par, 1),
	  T=par(L),
	  nonvar(Psi),
	  avl_domain(Psi, [P]),
	  \+(talkto(_,_)) ->
	  avl_fetch(P, Psi, Ext),
	  append(L, [seq(Ext)], L1),
	  T1=par(L1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  empty_avl(Psi1)
	/*
	nondet(P, A): instantiate P to a fresh constant.
	*/
	; functor(T, nondet, 2) ->
	  T = nondet(P, A),
	  %fresh_pred_sym(Proc),
	  make_instance(Proc),
	  copy_instantiate(A, P, Proc, T1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/*
	nondet(P, S, A): instantiate P to a fresh constant in set S.
	*/
	; functor(T, nondet, 3) ->
	  T = nondet(P, S, A),
	  %fresh_pred_sym(Proc),
	  make_instance(Proc),
	  assert(asserted(element(Proc, S))),
	  assert(asserted(fresh(Proc))),
	  copy_instantiate(A, P, Proc, T1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/* assume */
	; functor(T, assume, 1) ->
	  arg(1, T, Cons),
	  assert(asserted(Cons)),
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	; functor(T, seq, 1),
	  (   cleanup_seq(T, T1)->
	      Gamma1=Gamma,
	      Delta1=Delta,
	      Rho1=Rho,
	      Psi1=Psi
	  ;   T=seq([A|Rest]),
	      cleanup_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=seq([A1|Rest])
	  )
	; functor(T, par, 1),
	  T=par(L),
	  select(A, L, Rest),
	  cleanup_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	  select(A, L, A1, L1),
	  T1=par(L1)
	).

update_max_delta(T, Delta) :-
	term_size(Delta, Size),
	max_delta(Max, _, _),
	(   Size>Max->
	    retractall(max_delta(_,_,_)),
	    assert(max_delta(Size, T, Delta))
	;   true
	).
		       
	

cleanup_seq(T, T1) :-
	/*
	Applies on of the transformations:
	     seq([skip|As]) -->  seq([As]) and
             seq([A])       -->  A
	or fails, otherwise.
	*/
	functor(T, seq, 1),
	(   T=seq([A])->
	    T1=A
	;   T=seq([skip|B]),
	    B\==[]->
	    T1=seq(B)
	).

normalize_seq(T, T1) :-
	/*
	Recursively cleans up a sequential composition.
	*/
	(   nonvar(T),
	    cleanup_seq(T, T2) ->
	    normalize_seq(T2, T1)
	;   T1=T
	).

smaller_than(T, T1) :-
	/* T is either a proper subterm of T1 or skip. */
	(   T==skip
	;   T1\==T,
	    contains_term(T, T1)
	).


subsumed_by(T, T1) :-
/* All behaviour of T is also behaviour of T1. */
	(   T=T1->
	    true
	;   parse_recv(T,  _, P, Q, Type, V),
	    parse_recv(T1, _, P, Q, Type, V)->
	    true
	;   functor(T, par, 1),
	    functor(T1, par, 1),
	    T=par(L),
	    T1=par(L1),
	    permutation(L1, L2),
	    subsumed_by(L, L2)
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1)
	    do  subsumed_by(Arg, Arg1)->
		true
	    )
	).


mk_pair(A, B, Pair, Switched) :-
	(   Pair=par(A, B),
	    Switched=false
	;   Pair=par(B, A),
	    Switched=true
	).

mk_pair(A, B, Pair) :-
	mk_pair(A, B, Pair, _).

contains_skip(par(A,B)) :-
	(   A=skip
	;   B=skip
	).

unswitch_pair(par(A, B), Switched, Pair) :-
	(   Switched->
	    Pair=par(B, A)
	;   Pair=par(A, B)
	).

sanity_check(L) :-
	(   foreach(X, L)
	do  nonvar(X)->
	    true
	;   throw(parameter_not_instantiated(X-L))
	).
match(X, Exp) :-
	(   atomic(X),
	    simple(Exp)
	;   compound(X),
	    compound(Exp)->
	    functor(X, F, Arity),
	    functor(Exp, F, Arity)
	).

update_const_match(P, X, Exp, Rho, Rho1) :-
	(   atomic(X)->
	    avl_store(P-X, Rho, Exp, Rho1)
	;   same_functor(Exp, X),
	    (   foreacharg(ArgX, Exp),
		foreacharg(ArgExp, X),
		fromto(Rho, In, Out, Rho1),
		param(P)
	    do  update_const_match(P, ArgX, ArgExp, In, Out)
	    )
	;   Rho1=Rho
	).

propagate_const(P, X, Rho, X1) :-
	/*
	Substitute all assignments in rho for p's var x.
        If x's value is a composite term, recursively substitute
	assignments for its subterms.
	*/
	(   nonvar(X),
	    /*Process name can't occur as var.*/
	    X\==P, 
	    avl_member(P-X, Rho, X2)->
	    (   simple(X2) ->
		X1=X2
	    ;   compound(X2)->
		(   same_functor(X2, X1),
		    (   foreacharg(Arg, X2),
			foreacharg(Arg1, X1),
			param([P,Rho])
		    do  propagate_const(P, Arg, Rho, Arg1)
		    )
		)
	    )
	;   X1=X
	).

unpack_par(T, L) :-
	/*
	Unpack nested par-expressions into a list.
	*/
	(   functor(T, F, _),
	    F\==par->
	    L=[T]
	;   functor(T, par, 1)->
	    arg(1, T, L)
	;   functor(T, par, 2)->
	    arg(1, T, T1),
	    arg(2, T, T2),
	    unpack_par(T1, L1),
	    unpack_par(T2, L2),
	    append([L1,L2],L)
	).


intersect_avl(A, B, Res) :-
	/*
	Res contains all common assignments between A and B.
        Intersecting with full_avl preserves all constants.
	*/
	(   A==full_avl->
	    Res=B
	;   avl_domain(A, Dom),
	    (   foreach(Key, Dom),
		fromto(empty, In, Out, Res),
		param([A,B])
	    do  (   avl_fetch(Key, A, Val),
		    avl_fetch(Key, B, Val)->
		    avl_store(Key, In, Val, Out)
		;   In=Out
		)
	    )
	).
update_constants(P, X, V, Rho, Rho1) :-
	(   var(V) ->
	    Rho1=Rho
	;   functor(X, pair, 2),
	    functor(V, pair, 2),
	    X=pair(X1, X2),
	    V=pair(V1, V2) ->
	    update_constants(P, X1, V1, Rho, Rho2),
	    update_constants(P, X2, V2, Rho2, Rho1)
	;   ground(V) ->
	    avl_store(P-X, Rho, V, Rho1)
%	;   throw(pair-matching-error(X,V))
	).

substitute_constants(T, P, Rho, T1) :-
	/*
	In term T substitute all variable bindings defined in Rho to
	produce term T1. Throws exception if variable binding doesn't exist.
	*/
	avl_domain(Rho, Dom),
	(   foreach(Q-Var, Dom),
		fromto(T, In, Out, T1),
		param(Rho, P)
	    do  (  Q==P ->
		    avl_fetch(P-Var, Rho, Val),
		    substitute_term(Val, Var, In, Out)
		;   In=Out
		)
	).

check_cond(Cond, P, Rho) :-
	/*
	Check whether condition Cond holds under
	variable assignment Rho.
	*/
	(   Cond==true ->
	    true
	;   substitute_constants(Cond, P, Rho, Cond1),
	    catch(Cond1, _, fail)
	).

match_case(P, X, Cases, Rho, Rho1, Res) :-
	/*
	Match variable X of process p with Cases.
        Binds Res to the matching case or fails if no matching case exists.
	Cases=[C_1,C_2,...] with C_i=case(p, exp, A). Throws an exception if
	multiple cases match.
	*/
	propagate_const(P, X, Rho, X1),
	(   foreach(case(P, Exp, A), Cases),
	    fromto(none, In, Out, Res-Exp),
	    param([P, X1])
	do  (   match(X1, Exp)->
		(   In==none->
		    Out=A-Exp
		;   throw(cases-exp-double-match-between(X1,In,Exp))
		)
	    ;   In=Out
	    )
	),
	update_const_match(P, X1, Exp, Rho, Rho1).

is_valid(T) :-
	/*
	If it is in the basic set of axioms or was asserted.
	*/
	(  T=subset(S,S)
	;  T=prop_subset(emp,_)
	;  T=element(P, S),
	   asserted(element(P, S1)),
	   asserted(subset(S1, S))
	;  asserted(T)
	).

check_independent(P, Q) :-
	(   symset(P, S),
	    symset(Q, S1)->
	    tags_independent(S, S1)
	;   symset(P, S)->
	    tags_independent(S, Q)
	;   symset(Q, S)->
	    tags_independent(P, S)
	;   tags_independent(P, Q)
	).

clear_talkto :-
	retractall(talkto(_,_)).

set_talkto(P, Q) :-
	assert(talkto(P,Q)),
	assert(talkto(Q,P)).

init_independent(L) :-
	/*
	L=[(m,n),..] : processes m and n
	are independent.
	*/
	(   foreach((P,Q), L)
	do  assert(independent(P,Q)),
	    assert(independent(Q,P))
	).
make_instance(Inst) :-
	fresh_pred_sym(Inst).

cleanup :-
	clear_talkto,
	retractall(independent(_,_)),
	retractall(talkto(_,_)),
	retractall(symset(_,_)),
	retractall(in_remove),
	retractall(asserted(_)),
	retractall(max_delta(_,_,_)),
	reset_pred_sym.

rewrite(T, Rem, seq(Delta1), Rho1) :-
%	assert(cache_stats(0)),
	assert(max_delta(0, T, [])),
	Delta=[],
	empty_avl(Gamma),
	empty_avl(Rho),
	empty_avl(Psi),
	current_output(Out),
	open_null_stream(Null),
	set_output(Null),
	statistics(runtime, [Time0|_]),
	(
	 rewrite(T, Gamma, Delta, Rho, Psi, Rem, Gamma, Delta1, Rho1, Psi) ->
	 (
	  statistics(runtime, [Time1|_]),
	  Time is (Time1-Time0),
	  set_output(Out),
	  format('rewrite in: ~dms~n', [Time]),
	  set_output(Null)
	 );
	 (
	  statistics(runtime, [Time1|_]),
	  Time is (Time1-Time0),
	  set_output(Out),
	  format('rewrite in: ~dms~n', [Time]),
	  set_output(Null),
	  false
	 )
	).
 

rewrite_debug(T, Rem, _, _, Delta1, Rho1) :-
	(   rewrite(T, Rem, Delta1, Rho1) ->
	    true
	;   max_delta(_, TMax, DeltaMax),
	    format('Max rewritten term:~n~p~n with prefix:~n~p~n' ,[TMax,DeltaMax]),
	    fail
	).

format_result(Goal, Res) :-
	(   Goal->
	    Res='\e[32mpassed\e[0m'
	;   Res='\e[31mfailed\e[0m'
	).

unit_test :-
%	consult([examples]),
	format('================================================================~n',[]),
	format('~p:~30|~p~t~10+~p~t~13+~p~t~70|~n', ['Name','rewrite','race-check','time']),
	format('================================================================~n',[]),
	findall(T-Rem-Name-Ind, rewrite_query(T, Rem, Ind, Name), L),
	current_output(Out),
	open_null_stream(Null),
	(   foreach(T-Rem-Name-Ind, L),
	    param(Null, Out)
	do (
	     set_output(Null),
	     cleanup,
	     statistics(runtime, [Time0|_]),
	     format_result(catch(check_race_freedom(T, T1), _, fail), Race) ->
	     %findall(P-Q, tags_independent(P, Q), IndSet),
	     format_result(rewrite(T1, Rem, _, _), Rewrite)->
	     statistics(runtime, [Time1|_]),
	     Time is (Time1-Time0),
	     set_output(Out),
%	     format('Independent processes:~p~n',[IndSet]),
	     format('~p:~t~30|~p~t~21+~p~t~18+~t~d~3+~t ms~50|~n', [Name,Rewrite,Race,Time])
	   )
	),
	format('================================================================~n',[]).
