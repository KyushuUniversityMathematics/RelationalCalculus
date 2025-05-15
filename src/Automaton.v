From mathcomp Require Import fintype finset seq.
Require Import MyLib.RelationalCalculus.

Module main (def : Relation).

Module Basic_Lemmas := Basic_Lemmas.main(Rel_Set).
Module Relation_Properties := Relation_Properties.main(Rel_Set).
Module Functions_Mappings := Functions_Mappings.main Rel_Set.
Module Dedekind := Dedekind.main Rel_Set.
Module Conjugate := Conjugate.main Rel_Set.
Module Domain := Domain.main Rel_Set.
Module Sum := Sum_Product.main Rel_Set.
Module Tac := Tactics.main Rel_Set.
Module Pta := Point_Axiom.main Rel_Set.

Import Rel_Set Basic_Lemmas Relation_Properties Functions_Mappings Dedekind Conjugate Domain Sum Tac Pta.
Declare Scope automaton_scope.
Delimit Scope automaton_scope with AUTO.
Declare Scope language_scope.
Delimit Scope automaton_scope with LANG.

Structure automaton{state symbol:finType} :=
    {delta:symbol -> (Rel state state); init:Rel i state; final:Rel i state}.

Fixpoint dstar{state symbol:finType}(d:symbol -> (Rel state state))(w:seq symbol):(Rel state state):=
match w with
|nil => Id state
|s::w' => (d s) ・ (dstar d w')
end.
Definition accept{state symbol:finType}(M:@automaton state symbol)(w:seq symbol):Prop :=
(init M) ・ (dstar(delta M)w) ・ (final M)# = Id i.

Definition deterministic {state symbol:finType}(M:@automaton state symbol):Prop:=
(forall s:symbol,function_r(delta M s))/\function_r(init M).

Definition plusM{state1 state2 symbol:finType}(M:@automaton state1 symbol)(M':@automaton state2 symbol):automaton :=
    {|delta := fun x=>(@inl_r state1 state2)#・((delta M)x)・(@inl_r state1 state2)∪((@inr_r state1 state2) #・((delta M')x)・(@inr_r state1 state2)); init:=(init M)・(@inl_r state1 state2)∪((init M')・(@inr_r state1 state2)); final := (final M)・(@inl_r state1 state2)∪((final M')・(@inr_r state1 state2))|}.
Notation "M '+' M'" := (plusM M M') (at level 50, left associativity, 
                                      only parsing):automaton_scope.


Fixpoint delta_convert'{state:finType}(s:seq state)(R:Rel state state):state->Prop:=
match s with
|nil => fun x:state=>False
|h::s' => fun x:state=>R h x\/delta_convert' s' R x
end.
Definition delta_convert{state:finType}(s:{set state})(R:Rel state state):{set state}:=
[set x|is_true_inv((delta_convert'[seq x <- enum state | x \in s]R)x)].

Theorem NFA_DFA_equiv{symbol:finType}(w:seq symbol):
(exists (state:finType)(M:@automaton state symbol),accept M w) <-> (exists (state:finType)(M':@automaton state symbol),deterministic M'/\accept M' w).
split;move=>[state][M];[move=>H|by move=>[_ H];exists state,M].
exists (finset_set_of__canonical__fintype_Finite state).
destruct M.
exists {|delta:= fun (s:symbol)(x y:{set state})=>delta_convert x(delta0 s) = y;
         init:= fun (x:i)(y:{set state})=>[set x|is_true_inv(init0 tt x)]=y;
         final:= fun(x:i)(y:{set state})=>y:&:[set x|is_true_inv(final0 tt x)]<>set0|}.
split.
rewrite/deterministic.
split.
move=>s.
rewrite/=/function_r/total_r/univalent_r.
split.
move=>x y{}H.
have{}H:y=x;[done|subst].
by exists (delta_convert x(delta0 s)).
case=>alpha x.
case=>y{}H.
admit. 




Theorem plusP{state1 state2 symbol:finType}(M:@automaton state1 symbol)(M':@automaton state2 symbol)(w:seq symbol):
accept M w\/accept M' w <-> accept (M+M')%AUTO w.
Proof.
rewrite/accept.
split.
case=>H;
(have:Id i tt tt;[done|]);
rewrite-{1}H;
case=>b[]{H};
case=>a[]H H1 H2;
apply/inc_antisym_eq;
(split;[by rewrite unit_identity_is_universal|]=>x y);
destruct x,y=>_;
[move:(@inl_id state1 state2)|move:(@inr_id state1 state2)];
move/inc_antisym_eq=>[_ H3];
[have H4:Id state1 a a;[done|]|have H4:Id state2 a a;[done|]];
move:(H3 a a H4)=>{}H4;
case:H4=>a'[H4 H5];
[have H6:Id state1 b b;[done|]|have H6:Id state2 b b;[done|]];
move:(H3 b b H6)=>{}H6;
case:H6=>b'[H6 H7];
exists b';
(split;[exists a';split|]).
rewrite/=/cup/cupP.
exists (init M ・ inl_r state1 state2).
by split;[left|exists a].
move:a a'{H}H1 H4 H5.
elim:w.
simpl=>a a' H.
have{}H:a=b;[done|].
subst=>H1{}H2.
rewrite-inl_inr_cup_id/cup/cupP.
exists(inl_r state1 state2 # ・ inl_r state1 state2).
by split;[left|exists b].
move=>h w H a a'.
simpl.
case=>c[H1{}H2 H4 H5].
have H8:Id state1 c c;[done|].
move:(H3 c c H8)=>{}H8.
case:H8=>c'[H8 H9].
move:(H c c' H2 H8 H9)=>{}H.
exists c'.
split.
rewrite/cup/cupP.
exists((inl_r state1 state2 # ・ delta M h) ・ inl_r state1 state2).
by split;[left|exists c;split;[exists a|]].
done.
rewrite/=/cup/cupP/inverse.
exists(final M ・ inl_r state1 state2).
by split;[left|exists b].
rewrite/=/cup/cupP.
exists (init M' ・ inr_r state1 state2).
by split;[right|exists a].
move:a a'{H}H1 H4 H5.
elim:w.
simpl=>a a' H.
have{}H:a=b;[done|].
subst=>H1{}H2.
rewrite-inl_inr_cup_id/cup/cupP.
exists(inr_r state1 state2 # ・ inr_r state1 state2).
by split;[right|exists b].
move=>h w H a a'.
simpl.
case=>c[H1{}H2 H4 H5].
have H8:Id state2 c c;[done|].
move:(H3 c c H8)=>{}H8.
case:H8=>c'[H8 H9].
move:(H c c' H2 H8 H9)=>{}H.
exists c'.
split.
rewrite/cup/cupP.
exists((inr_r state1 state2 # ・ delta M' h) ・ inr_r state1 state2).
by split;[right|exists c;split;[exists a|]].
done.
rewrite/=/cup/cupP/inverse.
exists(final M' ・ inr_r state1 state2).
by split;[right|exists b].

move=>H;have :Id i tt tt;[done|];rewrite-{1}H.
case=>b'[].
case=>a'[].
case=>alpha[][]{}H;subst=>H H1.
case=>gamma[][]H2;subst=>H2.
left.
case:H=>a[H H3].
case:H2=>b[H2 H4].
apply/inc_antisym_eq;
(split;[by rewrite unit_identity_is_universal|]=>x y);
destruct x,y=>_.
exists b.
split.
exists a.
split.
done.
move:a' a H3 H1{H}.
elim:w.
simpl=>a' a H H1.
have{}H1:a'=b'.
done.
subst.
rewrite-(@inl_id _ state2).
by exists b'.
move=>h w H a' a H1.
simpl.
case=>c'[].
rewrite/cup/cupP.
case=>alpha[][]H3;subst.
case=>c[].
case=>d[]H3.
have:(inl_r state1 state2 ・ inl_r state1 state2 #) a d.
by exists a'.
rewrite inl_id=>H5.
have{}H5:a=d.
done.
subst=>H5 H6 H7.
move:(H c' c H6 H7)=>{}H.
by exists c.
case=>x[].
case=>y[]H5.
have:(inl_r state1 state2・inr_r state1 state2 #) a y.
by exists a'.
by rewrite inl_inr_empty.
done.

case:H=>a[]H H3.
case:H2=>b[]H2 H4.
exfalso.
move:a' a{H}H3 H1.
elim:w.
move=>a' a H1 H3.
have{}H5:a'=b'.
done.
subst.
have:(inl_r state1 state2・inr_r state1 state2 #) a b.
by exists b'.
by rewrite inl_inr_empty.
move=>h w H1 a' a H3.
simpl.
case=>c'[].
case=>alpha[][]H5;subst.
case=>c[]H5 H6 H7.
by move:(H1 c' c H6 H7).
case=>x[].
case=>y[]H5.
have:(inl_r state1 state2 ・ inr_r state1 state2 #) a y.
by exists a'.
by rewrite inl_inr_empty.
case:H=>a[H H2].
case=>alpha[][]H3;subst.
case=>b[]H3 H4.
exfalso.
move:w b' b{H3}H4 H1.
have{}H:(forall (b' : Datatypes_sum__canonical__fintype_Finite state1 state2)
(b : state1), inl_r state1 state2 b b' ->
dstar (delta (plusM M M')) nil a' b' -> False).
move=>b' b{}H H1.
have H3:a'=b'.
done.
subst.
have:(inr_r state1 state2・inl_r state1 state2 #) a b.
by exists b'.
by rewrite inr_inl_empty.
apply/(last_ind H)=>w t{}H b' b H1.
have H3:forall (d:symbol->Rel(Datatypes_sum__canonical__fintype_Finite state1 state2)(Datatypes_sum__canonical__fintype_Finite state1 state2))
(l:seq symbol)(t:symbol), dstar d(rcons l t) = (dstar d l)・(d t).
move=>d.
elim.
move=>t0.
by rewrite/= comp_id_l comp_id_r.
move=>h l H3 t0.
by rewrite/=H3 comp_assoc.
rewrite{}H3.
case=>c'[]H3.
case=>alpha[][]H4;subst.
case=>c[]H4 H5.
have:(inl_r state1 state2・inl_r state1 state2 #)b c.
by exists b'.
rewrite inl_id=>H6.
have{}H6:c=b.
done.
subst.
case:H4=>c[]H6.
by move:(H c' c H6 H3).
case=>x[_] {}H.
have:(inl_r state1 state2・inr_r state1 state2 #)b x.
by exists b'.
by rewrite inl_inr_empty.
case=>b[H3 H4].
right.
apply/inc_antisym_eq;
(split;[by rewrite unit_identity_is_universal|]=>x y);
destruct x,y=>_.
exists b.
split;[|done].
exists a.
split;[done|].
move:a' a H2 H1{H H3}.
elim:w.
simpl=>a' a H H1.
have{}H1:b'=a'.
done.
subst.
rewrite-(@inr_id state1).
by exists a'.
move=>h w H a' a H1.
simpl.
case=>c'[].
case=>alpha[][]H2;subst.
case=>c[].
case=>d[]H2.
have:(inr_r state1 state2・inl_r state1 state2 #)a d.
by exists a'.
by rewrite inr_inl_empty.
case=>c[].
case=>d[]H2.
have{}H2:(inr_r state1 state2・inr_r state1 state2 #)a d.
by exists a'.
have{}H2:d=a.
by rewrite inr_id in H2.
subst=>{}H1 H2 H3.
move:(H c' c H2 H3)=>{}H.
by exists c.
Qed.



