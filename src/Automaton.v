From mathcomp Require Import fintype seq.
Require Import MyLib.Basic_Notations_Set.

Import Rel_Set.
Structure automaton{state symbol:finType} :=
    {delta:symbol -> (Rel state state); init:Rel 'I_1 state; final:Rel 'I_1 state}.

Fixpoint dstar{state symbol:finType}(d:symbol -> (Rel state state))(w:seq symbol):(Rel state state):=
match w with
|nil => Id state
|s::w' => (d s) ・ (dstar d w')
end.
Definition accept{state symbol:finType}(M:@automaton state symbol)(w:seq symbol):Prop :=
(init M) ・ (dstar(delta M)w) ・ (final M)# = Id 'I_1.

Definition sum_rel{A B C D:eqType}(alpha:Rel A B)(beta:Rel C D):Rel(sum A C)(sum B D):=
fun x y =>
    match x, y with
    | inl a, inl b => alpha a b
    | inr c, inr d => beta c d
    | _, _ => False
    end.
Definition sum_rel_r{A B C:eqType}(alpha:Rel A B)(beta:Rel A C):Rel A(sum B C):=
fun x y =>
    match y with
    | inl y' => alpha x y'
    | inr y' => beta x y'
    end.
Definition plusM{state1 state2 symbol:finType}(M:@automaton state1 symbol)(M':@automaton state2 symbol):automaton :=
    {|delta := fun x=>sum_rel((delta M)x)((delta M')x); init:=sum_rel_r(init M)(init M'); final := sum_rel_r(final M)(final M')|}.

Lemma lt01:ssrnat.ltn 0 1. Proof. done. Qed.
Definition o:=Ordinal lt01.

    
Lemma plusP{state1 state2 symbol:finType}(M:@automaton state1 symbol)(M':@automaton state2 symbol)(w:seq symbol):accept M w\/accept M' w<->accept(plusM M M')w.
Proof.
    split.
    case;rewrite/accept=>H.
    have H1:forall x:state1, (init M)o x -> (init(plusM M M'))o(inl x);[done|].
    have H2:forall x y:state1, (dstar (delta M) w)x y -> (dstar (delta (plusM M M')) w)(inl x)(inl y).
    move=>x y{H}.
    elim w.
    rewrite/=/identity=>H.
    by subst.
    move=>a l H.
    simpl.
    rewrite/composite.

