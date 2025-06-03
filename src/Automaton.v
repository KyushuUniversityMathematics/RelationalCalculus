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
    {delta:symbol -> (Rel state state); init:Rel i state; final:Rel state i}.

Fixpoint dstar{state symbol:finType}(d:symbol -> (Rel state state))(w:seq symbol):(Rel state state):=
match w with
|nil => Id state
|s::w' => (d s) ・ (dstar d w')
end.
Definition accept{state symbol:finType}(M:@automaton state symbol)(w:seq symbol):Prop :=
(init M) ・ (dstar(delta M)w) ・ (final M) = Id i.
Notation " 'L' M " := (accept M) (at level 50, left associativity, 
                                      only parsing):automaton_scope.

Open Scope language_scope.
Definition language {symbol:finType}:=seq symbol->Prop.
Definition rev_l {symbol:finType}(l:language):language:=
fun s:seq symbol=>l (rev s).
Notation "l '^r'" := (rev_l l) (at level 30):language_scope.
Definition preimage_l {symbol:finType}(a:symbol)(l:language):language:=
fun w:seq symbol=> l (a::w).
Definition preimage_r {symbol:finType}(a:symbol)(l:language):language:=
fun w:seq symbol=> l (rcons w a).

Lemma preimage_assoc {symbol:finType}:forall(a b:symbol)(l:language),
preimage_r b (preimage_l a l) = preimage_l a (preimage_r b l).
Proof.
move=>a b l.
by rewrite/preimage_l/preimage_r.
Qed.

Definition preimage_lang_l {symbol:finType}(l l':language):language:=
fun v:seq symbol=>exists u, l u /\ l' (u++v).
Definition preimage_lang_r {symbol:finType}(l l':language):language:=
fun v:seq symbol=>exists u, l u /\ l' (v++u).

Lemma preimage_lang_assoc {symbol:finType}:forall(A B l:language),
forall w:seq symbol, preimage_lang_r B (preimage_lang_l A l) w <-> preimage_lang_l A (preimage_lang_r B l) w.
Proof.
move=>A B l w.
rewrite/preimage_lang_l/preimage_lang_r.
split=>[][]u[]H[]v[]H0 H1;exists v;(split;[done|]);exists u;(split;[done|]);
by rewrite catA in H1 *.
Qed.

Definition cup_lang{symbol:finType}(x y:language):language:=
fun s:seq symbol=>x s\/y s.
Notation "x '∪' y" := (cup_lang x y)(at level 50):language_scope.
Definition cap_lang{symbol:finType}(x y:language):language:=
fun s:seq symbol=>x s/\y s.
Notation "x '∩' y" := (cap_lang x y) (at level 50):language_scope.
Definition prod_lang{symbol:finType}(x y:language):language:=
fun s:seq symbol=>exists a b,s=a++b/\x a/\y b.
Notation "x '・' y" := (prod_lang x y) (at level 50):language_scope.
Definition phi{symbol:finType}:@language symbol := fun x=>False.
Definition eps{symbol:finType}:language := fun s:seq symbol=>s = nil.
Definition singl{symbol:finType}(s:symbol):language := fun x=> x = [::s].
Fixpoint power_l {symbol : finType}(n : nat)(l : @language symbol): language :=
  match n with
  | 0 => eps
  | S n' => l ・ power_l n' l 
  end.
Notation "l '^' n" := (power_l l n) (at level 30):language_scope.
Definition times_l{symbol:finType}(l:language):language:=
fun s:seq symbol=> exists n,power_l n l s.
Notation "l '^*'" := (times_l l) (at level 30):language_scope.
Definition plus_l{symbol:finType}(l:language):language:=
fun s:seq symbol=> exists n,power_l(S n)l s.
Notation "l '^+'" := (plus_l l) (at level 30):language_scope.
Definition comp_lang{symbol:finType}(l:language):language:=
fun s:seq symbol=>~ l s.
Notation "l '^c'" := (comp_lang l) (at level 30):language_scope.

Definition deterministic {state symbol:finType}(M:@automaton state symbol):Prop:=
(forall s:symbol,function_r(delta M s))/\function_r(init M).

Definition is_regular {symbol:finType}(l:language):Prop:=
exists (state:finType)(M:@automaton state symbol),forall w,l w <-> accept M w. 
Close Scope language_scope.

Definition plusM {state state' symbol:finType}(M:@automaton state symbol)(M':@automaton state' symbol):automaton :=
    {|delta := fun x=>Rel_sum(delta M x・@inl_r _ state')(delta M' x・@inr_r state _);
      init  := Rel_sum(init M #)(init M' #)#;
      final := Rel_sum(final M)(final M')|}.
Notation "M '+' M'" := (plusM M M') (at level 50, left associativity):automaton_scope.
Definition timesM {state state' symbol:finType}(M:@automaton state symbol)(M':@automaton state' symbol):automaton :=
    {|delta := fun s=>Rel_prod(fst_r state state'・delta M s)(snd_r state state'・delta M' s);
      init := Rel_prod(init M)(init M');
      final := Rel_prod(final M #)(final M' #)# |}.
Notation "M '×' M'" := (timesM M M') (at level 50, left associativity):automaton_scope.
Definition revM {state symbol:finType}(M:@automaton state symbol):=
    {|delta := fun x=>delta M x #; init  := final M #; final := init M # |}.
Definition concatM {state state' symbol:finType}(M:@automaton state symbol)(M':@automaton state' symbol):automaton:=
    {|delta := fun x =>( @inl_r _ state' #・delta M x・@inl_r _ state')∪(Rel_sum(final M・init M')(Id _)・delta M' x・@inr_r state _);
      init  := init M・(Rel_sum(Id _)(init M' #・final M #)#);
      final := (Rel_sum(final M・init M')(Id _))・final M'|}.
Definition phiM{symbol:finType}:@automaton _ symbol:= {|delta := fun x=>φ i i; init  := φ i i;final := φ i i|}.
Definition epsM{symbol:finType}:@automaton _ symbol:={|delta := fun x=>φ i i;init:=Id i;final:=Id i|}.
Definition singlM{symbol:finType}(s:symbol):automaton :=
    {|delta := fun (x:symbol)(a b:bool)=>a/\x=s/\not b;
      init  := fun (x:i)(a:bool)=>is_true a;
      final := fun (a:bool)(x:i)=>not (is_true a)|}.
Definition compM{state symbol:finType}(M:@automaton state symbol):automaton:=
    {|delta := delta M; init := init M; final := final M ^|}.
Definition plus_nfa {state symbol:finType}(M:@automaton state symbol):automaton :=
    {|delta := fun x=>(delta M x∪(delta M x・(final M・init M)));
      init  := init M;
      final := final M|}.


Lemma is_true_false:forall P, ~P <-> is_true_inv P = false.
Proof.
split=>H.
rewrite/is_true_inv.
move : (IndefiniteDescription.constructive_indefinite_description (fun b : bool => P <-> is_true b) (is_true_inv0 P)) =>[][]H0.
by rewrite H0 in H.
done.
case:(Classical_Prop.classic P);[move=>/is_true_id H0|done].
by rewrite H0 in H.
Qed.

Theorem NFA_DFA_equiv {state symbol:finType}(M:@automaton state symbol):
exists(state':finType)(M':@automaton state' _),deterministic M'/\
(forall w,accept M w <-> accept M' w).

destruct M.
exists _,{|delta:= fun (s:symbol)(x y:{set state})=>[set z | is_true_inv(exists2 w, w \in x & delta0 s w z)] = y;
         init:= fun (x:i)(y:{set state})=>[set x|is_true_inv(init0 tt x)]=y;
         final:= fun(y:{set state})(x:i)=>y:&:[set x|is_true_inv(final0 x tt)]<>set0|}.

split.
rewrite/deterministic/=.
split.
move=>s.
rewrite/=/function_r/total_r/univalent_r.
split.
move=>x y{}H.
have{}H:y=x;[done|subst].
by exists [set z | is_true_inv (exists2 w0 : state, w0  \in x & delta0 s w0 z)].
case=>alpha x[]y[]{}H H1.
rewrite/inverse in H.
by subst.
rewrite/=/function_r/total_r/univalent_r.
split.
move=>x y _.
destruct x,y.
rewrite/composite.
by exists [set x | is_true_inv (init0 tt x)].
case=>alpha x[]y[]{}H H1.
rewrite/inverse in H.
by subst.

move=>w.
rewrite/accept/=.
split.
have H:Id i tt tt;[done|move=>H1;rewrite-{}H1 in H].
Rel_simpl;[by rewrite unit_identity_is_universal|move=>[][] _].
case:H=>b[][]a[]H H1 H2.
rewrite comp_assoc.
exists [set x | is_true_inv (init0 tt x)].
split;[done|].
move:init0 a H H1.
elim:w.
move=>init0 a H H1.
have{}H1:b=a;[done|subst].
exists [set x | is_true_inv (init0 tt x)].
split;[done|].
rewrite/not=>H1.
have:a\in set0.
rewrite-H1!in_set(_:is_true_inv (init0 tt a));by apply/is_true_id.
by rewrite in_set0.
move=>h w H init0 a H1.
simpl=>[][]c[]H3 H4.
have H5:(init0・delta0 h)tt c.
by exists a.
rewrite comp_assoc.
exists [set z | is_true_inv
(exists2 w0 : state,
w0  \in [set x | is_true_inv (init0 tt x)] & delta0 h w0 z)].
split;[done|].
move:(H (init0 ・ delta0 h)c H5 H4).
rewrite(_:[set z | is_true_inv
(exists2 w0 : state,
w0  \in [set x | is_true_inv (init0 tt x)] & delta0 h w0 z)]=[set x | is_true_inv ((init0 ・ delta0 h) tt x)]).
done.
rewrite/composite.
apply/setP=>x.
rewrite!in_set.
have H6:forall P Q:Prop,(P<->Q) -> (is_true_inv P=is_true_inv Q).
move=>P Q{}H.
case_eq(is_true_inv P)=>{}H1;case_eq(is_true_inv Q)=>{}H2;[done| | |done].
by have:is_true_inv Q;[by apply/is_true_id/H/is_true_id|rewrite H2].
by have:is_true_inv P;[by apply/is_true_id/H/is_true_id|rewrite H1].
apply/H6.
split=>[][]y.
rewrite in_set=>/is_true_id{}H{}H1.
by exists y.
move=>[]{}H{}H1.
by exists y;[rewrite in_set;apply/is_true_id|].

move=>H.
have:Id i tt tt;[done|rewrite-{1}H].
move=>[]b[][]a[]{}H H0 H1.
Rel_simpl;[by rewrite unit_identity_is_universal|move=>[][] _].
have:exists b',b'\in b /\ final0 b' tt.
move:(H1)=>/eqP/set0Pn[]b'.
rewrite in_setI in_set=>/andP[]H2 H3.
exists b'.
by split;[|apply/is_true_id].
case=>b'[]H2 H3.
exists b'.
split;[|done].
have set0dstar:forall w,dstar (fun (s : symbol) (x : {set state}) =>
[eta eq [set z | is_true_inv (exists2 w : state, w  \in x & delta0 s
w z)]]) w set0 b -> False.
move{H0}=>{}w.
elim:w=>[|h w{}H].
rewrite/==>{}H.
have{}H:b=set0;[done|subst;by rewrite in_set0 in H2].

rewrite/==>[][]{}a[]H0.
have{}H0:a=set0.
rewrite-{}H0.
apply/setP=>x.
rewrite in_set in_set0.
apply/is_true_false=>[][]x0.
by rewrite in_set0.
by rewrite H0.

case_eq(a == set0)=>/eqP H4.
rewrite H4 in H0.
by move:(set0dstar _ H0).

move:{final0 H1 H3}init0 a H4 H H0.
elim:w=>[|h w H0]init0 a H4 H.
rewrite/==>H0.
have{}H0:b = a;[done|subst].
exists b'.
rewrite in_set in H2 *.
by move:(H2)=>/is_true_id.

rewrite/==>[][]c[]H1 H3.
move:(H0(init0・delta0 h)c)=>{}H0.
case_eq(c==set0)=>/eqP H5.
rewrite H5 in H3.
by move:(set0dstar _ H3).
move:(H5)=>/H0{}H0.
have H6:[set x | is_true_inv ((init0 ・ delta0 h) tt x)] = c.
rewrite-H1.
apply/setP=>x.
rewrite!in_set.
have{}H:(init0 ・ delta0 h) tt x <->exists2 w0 : state, w0  \in a & delta0 h w0 x.
split.
case=>a'[]{}H0{}H1.
exists a'.
rewrite-H in_set.
by apply/is_true_id.
done.
case=>a'.
rewrite-H in_set=>/is_true_id{}H{}H1.
by exists a'.
case_eq(is_true_inv ((init0 ・ delta0 h) tt x)).
move=>/is_true_id/H{}H0.
symmetry.
by apply/is_true_id.
rewrite-is_true_false=>{}H0.
symmetry.
apply/is_true_false/H/H0.

move:(H0 H6 H3)=>[]c'[][]a'[]{}H{}H0{}H1.
exists a'.
split.
done.
by exists c'.
Qed.

Open Scope language_scope.
Open Scope automaton_scope.
Theorem regular_cup {symbol:finType}(l l':@language symbol):
is_regular l/\is_regular l'->is_regular (l∪l').
Proof.
Close Scope language_scope.
rewrite/is_regular=>[][][]state[]M H[]state'[]M' H'.
exists (sum state state').
exists (M + M') => w.
rewrite/cup_lang{}H{}H'/accept.

suff H:(init (plusM M M') ・ dstar (delta (plusM M M')) w) ・ final (plusM M M') = 
((init M ・ dstar (delta M) w) ・ final M )∪((init M' ・ dstar (delta M') w) ・ final M').
rewrite{}H.
split=>[|H].
case=>H;[rewrite cup_comm|];
by rewrite H unit_identity_is_universal cup_universal.
rewrite-{}H.
case:( @unit_empty_or_universal((init M ・ dstar (delta M) w) ・ final M))=>H;
rewrite H cup_comm;[rewrite cup_empty|rewrite cup_universal];by[right|left].

destruct M,M';simpl.
move:init0 init1.
elim:w=>[|h w H]init0 init1.
by rewrite/=!comp_id_r sum_comp inv_invol inv_invol.
move:(H(init0・delta0 h)(init1・delta1 h))=>{}H.
rewrite/=-!comp_assoc-{}H.
f_equal.
by rewrite sum_comp/Rel_sum inv_cup_distr!comp_inv!inv_invol!comp_assoc.
Qed.


Open Scope language_scope.
Theorem regular_cap {symbol:finType}(l l':@language symbol):
is_regular l/\is_regular l'->is_regular (l ∩ l').
Proof.
Close Scope language_scope.
rewrite/is_regular=>[][][]state[]M H[]state'[]M' H'.
exists (prod state state').
exists (M × M')=>w.
rewrite/cap_lang{}H{}H'/accept.
suff H:(init (M × M') ・ dstar (delta (M × M')) w) ・ final (M × M') = 
((init M ・ dstar (delta M) w) ・ final M )∩((init M' ・ dstar (delta M') w) ・ final M').
rewrite{}H.
split=>[[H H']|H].
by rewrite H H' cap_idem.
case:(@unit_empty_or_universal ((init M ・ dstar (delta M) w) ・ final M))=>H0;rewrite H0 in H *.
rewrite cap_comm cap_empty in H.
move:unit_identity_not_empty.
by rewrite H.
rewrite cap_comm cap_universal in H.
by rewrite H unit_identity_is_universal.

destruct M,M';simpl.
move:init0 init1.
elim:w=>[|h w H]init0 init1.
by rewrite/=!comp_id_r sharpness/Rel_prod inv_cap_distr!comp_inv!(inv_invol (prod state state') _).
move:(H(init0・delta0 h)(init1・delta1 h))=>{}H.
rewrite/=-!comp_assoc-{}H.
repeat f_equal.
by rewrite{1 2}/Rel_prod!comp_assoc-sharpness-!comp_assoc/Rel_prod.

Open Scope language_scope.
Theorem regular_rev{symbol:finType}(l:@language symbol):
is_regular l -> is_regular (l^r).
Proof.
Close Scope language_scope.
rewrite/is_regular=>[][]state[]M H.
exists state,(revM M)=>w.
rewrite/rev_l{l}H/accept/revM/=.
have H:forall (d:symbol->Rel state state)(w:seq symbol)(h:symbol),dstar d (rcons w h)=dstar d w・d h.
move=>d{}w h.
elim:w;[by rewrite/=comp_id_l comp_id_r|]=>a w H.
by rewrite/=comp_assoc H.
have{}H:dstar (fun x : symbol => delta M x #) w = dstar (delta M) (rev w) #.
elim:w;[by rewrite inv_id|]=>h w H0.
by rewrite/={}H0 rev_cons H comp_inv.
by split=>H0;rewrite-inv_id-{}H0!comp_inv inv_invol comp_assoc H.
Qed.


Open Scope language_scope.
Theorem regular_prod{symbol:finType}(l l':@language symbol):
is_regular l /\ is_regular l' -> is_regular(l・l').
Proof.
Close Scope language_scope.
rewrite/is_regular/accept/prod_lang=>[][][]state[]M H[]state'[]M' H'.
exists (sum state state'),(concatM M M')=>w.
remember (delta (concatM M M')) as d.
remember (final (concatM M M')) as f.
destruct M,M'.
rewrite/= in H H' Heqd Heqf*.

have{H'}H:(exists a b : seq symbol, w = a ++ b /\ l a /\ l' b)<->
(exists a b : seq symbol, w = a ++ b /\
(init0 ・ dstar delta0 a) ・ final0 = Id i /\
(init1 ・ dstar delta1 b) ・ final1 = Id i).
split=>[][]a[]b[]{}H0[]H1 H2;exists a,b;
by[rewrite-H-H'|rewrite H H'].
rewrite{l l'}H-Heqd-Heqf.

have inil:forall init:Rel i state,init ・ Rel_sum (Id state) (init1 # ・ final0 #) #・inl_r state state'# = init.
move=>init.
by rewrite comp_assoc/Rel_sum comp_id_r inv_cup_distr!comp_inv
2!inv_invol(inv_invol _ _(inr_r _ _))comp_cup_distr_r!comp_assoc
inl_id inr_inl_empty!comp_empty_r cup_empty comp_id_r.

have inir:forall init:Rel i state,init ・ Rel_sum (Id state) (init1 # ・ final0 #) #・inr_r state state'#= init・final0・init1.
move=>init.
by rewrite!comp_assoc/Rel_sum comp_id_r inv_cup_distr inv_invol!comp_inv
inv_invol(inv_invol _ _(inr_r _ _))comp_cup_distr_r!comp_assoc
inl_inr_empty inr_id cup_comm cup_empty comp_id_r.

have rf:inr_r state state'・f = final1.
rewrite Heqf-comp_assoc-{2}(@comp_id_l _ _ final1).
f_equal.
by rewrite/Rel_sum comp_cup_distr_l-!comp_assoc inr_inl_empty inr_id
!comp_empty_l cup_comm comp_id_l cup_empty.

have lf:inl_r state state'・f = final0・(init1・final1).
rewrite Heqf-!comp_assoc.
f_equal.
by rewrite/Rel_sum comp_cup_distr_l-!comp_assoc inl_inr_empty inl_id
comp_empty_l comp_id_l cup_empty.

have {Heqf}inif:forall init:Rel i state,init ・ Rel_sum (Id state) (init1 # ・ final0 #) #・f = init・final0・(init1・final1).
move=>init.
rewrite Heqf!comp_assoc.
f_equal.
rewrite-!comp_assoc.
f_equal.
by rewrite sum_comp comp_inv 2!inv_invol inv_id comp_id_l comp_id_r cup_idem.

have rdstar:forall w,inr_r state state'・dstar d w = dstar delta1 w・inr_r state state'.
elim=>[|h{}w H].
by rewrite/=comp_id_l comp_id_r.
by rewrite/=-comp_assoc{1}Heqd/Rel_sum!comp_cup_distr_r!comp_cup_distr_l
-!comp_assoc inr_id inr_inl_empty!comp_empty_l!comp_id_l cup_comm
cup_empty cup_comm cup_empty!comp_assoc H.

have rdstarf:forall w,inr_r state state'・(dstar d w・f) = dstar delta1 w・final1.
move=>{}w.
by rewrite-comp_assoc rdstar comp_assoc rf.

have dstarl:forall w,dstar d w・inl_r state state'# =
inl_r state state'#・dstar delta0 w.
elim=>[|h{}w H].
by rewrite/=comp_id_l comp_id_r.
rewrite/=comp_assoc{}H-!comp_assoc.
f_equal.
by rewrite Heqd/Rel_sum!comp_cup_distr_r!comp_assoc inr_inl_empty inl_id
comp_id_r comp_id_l!comp_empty_r!cup_empty.

have inidstarl:forall (init:Rel i state)(w:seq symbol),init ・ Rel_sum (Id state) (init1 # ・ final0 #) #・dstar d w・inl_r state state'# =init・dstar delta0 w.
move=>init{}w.
by rewrite comp_assoc dstarl-comp_assoc inil.

have{}Heqd:forall h,d h = inl_r state state'#・delta0 h・inl_r state state'∪
(inl_r state state'#・final0・init1・delta1 h・inr_r state state')∪
(inr_r state state'#・delta1 h・inr_r state state').
move=>h.
by rewrite Heqd/Rel_sum comp_id_r cup_assoc!comp_cup_distr_r!comp_assoc.

split=>[[]a[]b[]H[]H0 H1|H].
rewrite{w}H(_:dstar d(a++b)=dstar d a・dstar d b);[|
by elim:{H0}a=>[|h a H];[rewrite/=comp_id_l|rewrite/=H comp_assoc]].

rewrite-(comp_id_r _ _(dstar d a))-inl_inr_cup_id comp_cup_distr_l
!comp_cup_distr_r comp_cup_distr_l comp_cup_distr_r-!comp_assoc inidstarl.
suff:((((init0 ・ dstar delta0 a) ・ inl_r state state') ・ dstar d b) ・ f)=Id i.
move=>H2.
by rewrite H2 unit_identity_is_universal cup_comm cup_universal.

move:H1.
elim:b=>[|h b H].
rewrite/=!comp_id_r=>H.
by rewrite!comp_assoc lf H comp_id_r-comp_assoc H0.
rewrite/=-!comp_assoc=>H1.

by rewrite(comp_assoc i state)Heqd comp_cup_distr_l-!comp_assoc
inl_inr_empty!comp_empty_l cup_empty!comp_assoc-comp_cup_distr_l
comp_assoc-(comp_assoc state(sum _ _))inl_id comp_id_l
!comp_cup_distr_r!comp_cup_distr_l!comp_assoc rdstarf-!comp_assoc
H0 comp_id_l H1 unit_identity_is_universal cup_universal.

move:init0 H.
elim:w=>[|h w H]init0.
rewrite/=comp_id_r inif.
case:(@unit_empty_or_universal (init1 ・ final1))=>H.
rewrite H!comp_empty_r=>{}H.
move:unit_identity_not_empty.
by rewrite H.
rewrite H-unit_identity_is_universal comp_id_r=>H0.
exists nil,nil.
by rewrite/=!comp_id_r H H0 unit_identity_is_universal.

rewrite/=Heqd!comp_cup_distr_r!comp_cup_distr_l comp_cup_distr_r
-!comp_assoc inil inir comp_cup_distr_r!comp_assoc  rdstarf
cup_assoc cup_idem.
case:(@unit_empty_or_universal(init0 ・ (delta0 h ・ (inl_r state state' ・ (dstar d w ・ f)))))=>H1.
rewrite H1 cup_comm cup_empty-comp_assoc=>{}H1.
case:(@unit_empty_or_universal(init0 ・ final0))=>H2.
rewrite H2 comp_empty_l in H1.
move:unit_identity_not_empty.
by rewrite H1.
rewrite H2-unit_identity_is_universal comp_id_l in H1.
exists nil,(h::w).
by rewrite/=comp_id_r!comp_assoc H1 H2 unit_identity_is_universal.
move=>_.
have:((init0・ delta0 h ・ Rel_sum (Id state) (init1 # ・ final0 #) #) ・ dstar d w)・ f = Id i.
by rewrite-(comp_id_l _ _(dstar d w))-inl_inr_cup_id!comp_assoc
!comp_cup_distr_r!comp_cup_distr_l-!comp_assoc inil!comp_assoc H1
cup_comm cup_universal unit_identity_is_universal.
move/H=>[]a[]b[]{}H[]H0 H2.
exists (h::a),b.
by rewrite/=H-!comp_assoc H0 H2.
Qed.

Theorem regular_phi{symbol:finType}:@is_regular symbol phi.
Proof.
rewrite/is_regular.
exists i,phiM=>w.
by split;[|rewrite/accept/=!comp_empty_l=>H;move:unit_identity_not_empty;rewrite H].
Qed.
Theorem regular_eps{symbol:finType}:@is_regular symbol eps.
rewrite/is_regular.
exists i,epsM.
rewrite/accept.
case=>[|a l].
by split=>[_|];[rewrite/=!comp_id_l|].
rewrite/=comp_empty_l!comp_empty_r comp_empty_l.
by split=>[|H];[|move:unit_identity_not_empty;rewrite H].
Qed.

Theorem regular_singl{symbol:finType}(s:symbol):is_regular(singl s).
Proof.
rewrite/is_regular.
exists bool,(singlM s).
rewrite/accept/inverse=>w.
have H:forall a,a = Id i <-> a tt tt.
move=>a.
split=>H.
by rewrite H.
by case:( @unit_empty_or_universal a)=>H0;[rewrite H0 in H|rewrite H0 unit_identity_is_universal].

rewrite H.
case:w=>[|a[|b l]].
split;[done|].
by rewrite/=comp_id_r=>[][][[_]|[]].
case_eq(s == a)=>/eqP{}H.
subst.
split=>[_|];[|done].
exists false.
split.
exists true.
by rewrite/=comp_id_r.
done.
(split;rewrite/singl)=>[[]H1|[]];[by subst|case=>[][]];[by simpl|].
case=>[][[_]|[]].
rewrite/=comp_id_r=>[][] _ [] H0.
by subst.
done.
split.
done.
case=>[][][].
by simpl.
case=>[][[] _|[]];[|done].
rewrite/==>[][][][][] _ [] H0.
done.
subst=>_.
by case=>x[][].
Qed.

Open Scope language_scope.
Theorem regular_comp{symbol:finType}(l:@language symbol):
is_regular l -> is_regular (l^c).
Proof.
Close Scope language_scope.
rewrite/is_regular/comp_lang=>[][]state[]M H.
move:(NFA_DFA_equiv M)=>[]state'[]M'[]H0 H1.
exists _,(compM M')=>w.
rewrite{l}H{state M}H1.

rewrite/accept/=.
move:H0.
rewrite/deterministic=>[][]H H0.
have{H0}H:function_r(init M'・dstar(delta M')w).
destruct M';rewrite/= in H H0 *.
move:init0 H0.
elim:w=>[|h w H1]init0 H0.
by rewrite/=comp_id_r.
rewrite/=-comp_assoc.
apply/H1/function_comp/H/H0.
have H0:exists x, (init M'・dstar(delta M')w)tt x.
rewrite/function_r/total_r in H.
move:H=>[]{}H _.
have H0:Id i tt tt;[done|].
move:(H tt tt H0)=>[]x[]{H0}H _.
by exists x.
case:H0=>x H0.
have{}H:forall y,(init M' ・ dstar (delta M') w) tt y -> y=x.
move=>y H1.
rewrite/function_r/univalent_r in H.
move:H=>[] _ H.
have{H1}H0:((init M' ・ dstar (delta M') w) # ・ (init M' ・ dstar (delta M') w))x y.
by exists tt.
by move:(H _ _ H0).

have{H0}H:forall R:Rel state' i,
(init M' ・ dstar (delta M') w) ・ R = Id i <-> R x tt.
move=>R.
split=>H1.
have:Id i tt tt;[done|rewrite-H1].
case=>y[]/H{}H.
by subst.
by Rel_simpl=>[][][] _;[|exists x].
by rewrite/not!H/complement/rpc.
Qed.

Theorem power_regular {symbol:finType}(l:@language symbol)(n:nat):
is_regular l -> is_regular(power_l n l).
Proof.
move=>H.
elim:n=>[|n H0].
apply/regular_eps.
by apply/regular_prod.
Qed.

Lemma dstar_cat {state symbol:finType}:
forall(d:symbol->Rel state state)(a b:seq symbol),
dstar d(a++b) = dstar d a・dstar d b.
Proof.
move=>d a b.
elim:a=>[|h a H].
by rewrite/=comp_id_l.
by rewrite/=H comp_assoc.
Qed.
Lemma nil_rcons {symbol:Type}(s:seq symbol):s = nil \/exists t s',s=rcons s' t.
Proof.
elim:s=>[|h s[H|[]h'[]s']];[by left| |];right;
[exists h,nil|exists h',(h::s')];by subst.
Qed.
Lemma dstar_rcons {state symbol:finType}:
forall(d:symbol->Rel state state) w t,
dstar d(rcons w t) = dstar d w・d t.
Proof.
move=>d w t.
elim:w=>[|h w H].
by rewrite/=comp_id_l comp_id_r.
by rewrite/=H comp_assoc.
Qed.


Fixpoint take_reg {state symbol:finType}(init0:Rel i state)
(delta0:symbol->Rel state state)(final0:Rel state i)(w:seq symbol)(n:nat):nat:=
match n with
|0 => size w
|S n' =>
  if is_true_inv(init0・dstar delta0(take n w)・final0 = Id i)
  then n
  else take_reg init0 delta0 final0 w n'
end.

Theorem plus_regular {symbol:finType}(l:@language symbol):
is_regular l -> is_regular(plus_l l).
Proof.
rewrite/is_regular=>[][]state[]M H.
exists _, (plus_nfa M)=>w.
destruct M.
rewrite/accept/plus_l/= in H *.

remember(fun x : symbol =>
delta0 x ∪ (delta0 x・(final0 ・ init0)))as d.

split.
case=>n.

have H0:forall w, ((init0 ・ dstar delta0 w) ・ final0)
⊆ ((init0 ・ dstar d w) ・ final0).
move=>{}w.
apply/comp_inc_compat_ab_a'b/comp_inc_compat_ab_ab'.
elim:w=>[|h{}w{}H];[done|simpl=>x z[]y[]H0 H1].
exists y.
rewrite{1}Heqd.
by split;[apply/cup_l|apply/H].

move:w.
elim:n=>[|n H1]w.
rewrite/=/prod_lang=>[][]a[][|b' b[] _[] _];[|done].
rewrite cats0=>[][]H1[]/H{}H _.
subst.
apply/inc_antisym_eq.
by split;[rewrite unit_identity_is_universal|rewrite-{}H].

rewrite/={1}/prod_lang=>[][]a[]b[]H2[]/H{}H/H1{}H1.
rewrite{w}H2 dstar_cat.
move:H.
have H:(forall x:seq symbol,x = nil \/exists h x', x = rcons x' h).
elim=>[|h x H];[by left|right].
case:H=>H.
exists h,nil.
by subst.
case:H=>x0[]x1 H.
subst.
by exists x0,(h::x1).
case:(H a)=>[|[]t[]a']{}H.
by rewrite{a}H/=comp_id_l.
rewrite{a}H.
have dstar_rcons:forall d,dstar d(rcons a' t) = dstar d a'・d t.
move=>t0{Heqd H0 H1}d.
elim:a'=>[|h a H].
by rewrite/=comp_id_r comp_id_l.
by rewrite/=H comp_assoc.
rewrite!dstar_rcons=>H.
rewrite{2}Heqd-!comp_assoc!comp_cup_distr_l!comp_cup_distr_r-!comp_assoc.
have{}H:init0・dstar d a'・delta0 t・final0 = Id i.
apply/inc_antisym_eq.
split;[by rewrite unit_identity_is_universal|rewrite-{}H!comp_assoc].
apply/comp_inc_compat_ab_ab'/comp_inc_compat_ab_a'b.
elim:{dstar_rcons}a'=>[|h a H].
done.
rewrite/={1}Heqd comp_cup_distr_r comp_assoc-comp_cup_distr_l.
apply/comp_inc_compat_ab_ab'=>x y/H.
apply/cup_l.
by rewrite H comp_id_l H1 unit_identity_is_universal cup_universal.

move=>H0.
have:exists u v, w = u ++ v /\ size v <= size w - 1 /\
  init0・dstar delta0 u・final0・init0・dstar d v・final0 = Id i.
have:Id i tt tt by [].
rewrite-{1}H0=>[][]b[][]a[]{}H0 H1 H2.
have:exists n, (take(S n)w = w/\(dstar delta0(take(S n)w)・final0) a tt) \/
(dstar delta0(take(S n)w)・final0) a tt /\(init0・dstar d(drop(S n)w))tt b.
move:a{H0}H1.
elim:w=>[|h w H0]a.
rewrite/=comp_id_l comp_id_r=>H1.
have{}H1:a = b;[done|subst].
exists 0.
by left.
rewrite/==>[][]c[]H1/H0[]n[][]{}H0 H3.
rewrite Heqd in H1.
case:H1=>alpha[][]H' H1;rewrite{alpha}H' in H1.
exists (S n).
rewrite H0 in H3 *.
left.
split;[done|].
rewrite comp_assoc.
by exists c.

exists 0.
right.
rewrite take0 drop0/=comp_id_r.
rewrite H0 in H3 *.
rewrite-comp_assoc in H1.
case:H1=>[][][]H1 H4.

by rewrite/=comp_id_l comp_id_r.
simpl.
elim:w.
rewrite/=!comp_id_r.
remember a as a'.
rewrite{}Heqa' in H1.
move:a H1.
elim:w=>[a H1|h w H1 a].
have{}H1:a'=b;[done|subst].
exists 0.
rewrite/=comp_id_l comp_id_r.
have H3:a' = b -> 

have H3: final0 b tt /\ init0 tt b.
move=>{}H.
rewrite H/= in H1.
by have{}H1:a = b;[|subst]. *)
move:a{H0}H1 H2.

elim:w=>[|h w H0]a H1 H2.
rewrite/=comp_id_l in H1 *.
exists 0.
(* have:(nil:seq symbol)=nil;[done|]=>/H3{}H3. *)
by have{}H1:a=b;[|subst].

rewrite/= in H1 *.
case:H1=>c[]H1 H'.
(* have{}H3:(w = [::] -> final0 b tt /\ init0 tt b). *)
(* move=>H4.
rewrite H4/= in H'. *)

(* apply/H3. *)
move:(H0 _ H' H2)=>[]n[]{}H0.
rewrite Heqd/cup/cupP in H1.
case:H1=>alpha[][]H1 H4;rewrite{alpha}H1 in H4.
exists (S n).
rewrite comp_assoc.
by split;[exists c|].
exists 0.
rewrite take0 drop0/=comp_id_r.
rewrite-comp_assoc in H4.
case:H4=>[][][]H1 H4.
by split;[|exists c].

case=>n[]H3 H4.
exists (take(S n)w),(drop(S n)w).
rewrite cat_take_drop.
split;[done|].
split.
rewrite size_drop.
case:(size w)=>[|n'];[done|].
rewrite/=ssrnat.subSS PeanoNat.Nat.sub_0_r ssrnat.subnE.
apply/PeanoNat.Nat.le_sub_l.
remember(take(S n)w)as u.
remember(drop(S n)w)as v.

have H5:init0・dstar delta0 u・final0 = Id i.
apply/inc_antisym_eq.
split;[by rewrite unit_identity_is_universal|move=>[][] _].
rewrite comp_assoc.
by exists a.
rewrite H5 comp_id_l.
apply/inc_antisym_eq.
split;[by rewrite unit_identity_is_universal|move=>[][] _].
by exists b.
case_eq(w == nil)=>/eqP H5.
rewrite H5/=comp_id_r in H1 *.
by have{}H1:a = b;[|subst;exists b].
have{}H5:take(S n)w <> nil.
case=>H6.
have:size(take (S n) w)=0 by rewrite{}H6.
rewrite size_take.
case:(ssrnat.leq (S (S n)) (size w));[done|].
move:{H1 H3 H4 H6}H5.
by case:w.
rewrite-(cat_take_drop(S n)w)dstar_cat in H1.
case:H1=>c[]H1{}H4.
exists b.
split;[|done].
exists c.
split;[|done].
have{}H1:dstar d()
have H5:take (S n) w = nil -> init0 tt c.
move=>H5.
rewrite H5/= in H1.
by have{}H1:a = c;[|subst].
move:a H1 H3 H5{H0}.
elim:(take(S n)w)=>[|h t H1]a.
move=>_ _ H1.
by have:(nil:seq symbol) = nil=>[|/H1].
rewrite/==>[][]e[]H3/H1{}H1.

rewrite/==>_{}H1.
have{}H1:a = c by [].
by subst.
rewrite/=.
case:H1=>t[]s H1.
rewrite H1!dstar_rcons{2}Heqd comp_cup_distr_l.

elim:(take(S n)w)=>[|a0 l0 H1].
rewrite/==>_ H1.


move=>[][] _.
Search ( _ - _ <= _).
done.
case:w.
case_eq(take(S n)w)=>H4.
have:size(take(S n)w)=0 by rewrite H4.
rewrite size_take.

rewrite/not.
remember (take(S n)w) as u.
have{H0 H1 H2}

case:H2=>d[]H1[][][]H2 H5.
exists (S n),e.
split.


done.
H3 H4.
subst.


rewrite/={1}Heqd/cup/cupP=>[][]c[][]alpha[][]H1 H2 H3;[left|right].


rewrite/={1}Heqd/cup/cupP=>H1[]c[][]alpha[][]H2 H3 H4 H5.
admit.
subst.
case:H3=>d[]H3[][][]H6 H7.
move:(H0 a b H1).
move:(H0 c b )
exists (S n),c.
rewrite H2.
rewrite Heqd

have H1:exists n, init0・dstar delta0(take(S n)w)・final0 = Id i.

(* have:size w < S(size w) by [].
remember(S(size w))as n=>{Heqn}.
move:w.
elim:n=>[|n H0]w.
by move/PeanoNat.Nat.nlt_0_r.
move=>H1 H2. *)
exists (take_reg init0 delta0 final0 w (size w)).


move=>H0.
have H1:exists n, init0・dstar d(take n w)・final0 = Id i.
move:H0.
elim:w=>[|h w{}H].
rewrite/=comp_id_r=>{}H.
by exists 0.

have{}H0:exists n,
init0・dstar d(take(S n)w)・final0・init0・dstar delta0(drop(S n)w)・final0 = Id i.
case:(Classical_Prop.classic (exists n : nat,
((((init0 ・ dstar d (take (S n) w)) ・ final0) ・ init0)
・ dstar delta0 (drop (S n) w)) ・ final0 = Id i)).
done.
move/Classical_Pred_Type.not_ex_all_not=>H1.
exfalso.
have [n]: exists n : nat, True by exists 0.
move:(H1 n)=>{}H1.
exfalso.
move:H1.
elim:n.

fix_rcons
Search (~ (_ /\ _)).
move=> (n0 : nat).
pose n:nat.
move=>n.
move=>n.
elim:H1.
Search (~ (exists _, _)). 
move:H0.
elim:w=>[|h w H0].
rewrite H/=.
by left.
rewrite/=comp_assoc{1}Heqd!comp_cup_distr_r comp_cup_distr_l-!comp_assoc=>H1.
case:( @unit_empty_or_universal (init0・delta0 h・dstar d w・final0))=>H2.
rewrite{}H2 cup_comm cup_empty in H1.
right.
case:( @unit_empty_or_universal((init0 ・ delta0 h) ・ final0))=>H2.
rewrite H2!comp_empty_l in H1.
move:unit_identity_not_empty.
by rewrite H1.
rewrite-unit_identity_is_universal in H2.
rewrite H2 comp_id_l in H1.
exists [::h],w.
by rewrite/=comp_id_r H2 H1.
left.
rewrite H/=unit_identity_is_universal-!comp_assoc .







case:(Classical_Prop.classic(exists n : nat, prod_lang l (power_l n l) w)).
done.
rewrite/not=>H0 H1.
exfalso.
case:H0.
exfalso.
apply/contrapositive.


case:w=>[|h w].
rewrite/=/prod_lang=>H0.
exists 0,nil,nil.
by rewrite H/=.



rewrite/={1}Heqd!comp_cup_distr_r comp_cup_distr_l comp_cup_distr_r
comp_id_l-!comp_assoc=>H0.
have{}H0:(((init0 ・ delta0 h) ・ dstar d w) ・ final0) = Id i.
case:( @unit_empty_or_universal (init0・final0))=>H1.
by rewrite H1!comp_empty_l cup_empty in H0.
by rewrite H1-unit_identity_is_universal comp_id_l cup_idem in H0.




have H0:forall w,plus_l l w -> l w \/ (exists u v, w = u ++ v/\l u /\ plus_l l v).
move=>{}w[]n.
move:n w.
elim=>[|n];[left|].
by case:p=>a[][[]H0[]H1 _|b' b[] _ [] _];[rewrite H0 cats0|].

remember (S n) as n'=>H0 w.
rewrite/==>[][]a[]b[]H1[]H2/H0[];right.
exists a,b.
split;[done|split;[done|]].
exists 0,b,nil.
by rewrite cats0.
exists a,b.
split;[done|split;[done|]].
rewrite/plus_l.
exists 0.
case=>x[]y[].
rewrite/power_l


done.
case=>[][[]a[][[]H0[]H1 _|b' b[] _ [] _]|n].
rewrite cats0 in H0.
left.
by subst.
done.
rewrite/=
case=>a[]b.



case:w=>[|h w].
rewrite/=/prod_lang=>H0.
exists 0,nil,nil.
by rewrite H/=.

rewrite/={1}Heqd!comp_cup_distr_r!comp_cup_distr_l!comp_cup_distr_r
comp_id_l-!comp_assoc=>H0.
have{}H0:(((init0 ・ delta0 h) ・ dstar d w) ・ final0) = Id i.
case:( @unit_empty_or_universal (init0 ・ final0))=>H1;rewrite H1 in H0.
by rewrite!comp_empty_l cup_empty in H0.
by rewrite-unit_identity_is_universal comp_id_l cup_idem in H0.
rewrite/prod_lang.
exists 0.
split;[done|split=>[|]].
rewrite/=.



rewrite/=!comp_cup_distr_r!comp_cup_distr_l!comp_cup_distr_r!comp_id_l=>H2.

Search (_ ⊆ (_ ∪ _)).
rewrite/==>H.
Search ((_ ・_)⊆(_・_)).
apply/

admit.

elim:w=>[|h w H0].
rewrite/=comp_id_r/prod_lang=>H0.
exists 0,nil,nil.
by rewrite H/=comp_id_r.
rewrite/=-comp_assoc.


rewrite/=comp_id_r/prod_lang.
split=>[|H0].
case=>n[][|a' a][][|b' b][];[|done|done|done].
by rewrite H/=comp_id_r=>[] _[]{}H.
exists 0,nil,nil.
by rewrite H/=comp_id_r.

split.

move:H.
simpl.
simpl.

simpl.
done.
done.
done.



split.
case=>x.
rewrite/prod_lang.
elim:x=>[|n H0].
rewrite/=/prod_lang/eps=>[][]a[]b[]H0[]/H{}H H1.
rewrite{b}H1 cats0 in H0.
subst.

apply/inc_antisym;[by rewrite unit_identity_is_universal|rewrite-{}H].
apply/comp_inc_compat_ab_a'b/comp_inc_compat_ab_ab'.
elim:a=>[|h w H];[done|].
rewrite/=comp_cup_distr_r comp_id_l.
apply/(inc_trans state state(delta0 h・dstar delta0 w)
(delta0 h・dstar (fun x : symbol => (Id state ∪ (final0 ・ init0)) ・ delta0 x)w )
((delta0 h ∪ ((final0 ・ init0) ・ delta0 h))
・ dstar (fun x : symbol => (Id state ∪ (final0 ・ init0))
・ delta0 x) w))/comp_inc_compat_ab_a'b/cup_l/comp_inc_compat_ab_ab'/H.

rewrite/=.

remember (S n) as n'=>{n Heqn'}
.


simpl.



Search (_⊆(_∪_)).
apply/inc_comp_r.

Rel_simpl.
by rewrite unit_identity_is_universal.
case:H=>H _.
apply (inc_trans i i ((init0 ・ dstar delta0 a) ・ final0)(Id i)
((init0
・ dstar (fun x : symbol => (Id state ∪ (final0 ・ init0))
・ delta0 x) a) ・ final0) H).
apply/H.
simpl.


admit.
move.