Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Tactics.

Check Tactics.total_comp.

Lemma sample {A : eqType} {alpha : Rel A A}: alpha ⊆ Id A -> alpha # = alpha.
Proof.
move => H.
assert (alpha # ⊆ alpha).
move : (@dedekind1 _ _ _ (alpha #) (Id A) (Id A)) => H0.
rewrite comp_id_r comp_id_r inv_invol in H0.
replace (alpha # ∩ Id A) with (alpha #) in H0.
replace (Id A ∩ alpha) with alpha in H0.
apply (@inc_trans _ _ _ (alpha # ・ alpha)).
apply H0.
apply comp_inc_compat_ab_b.
rewrite -inv_inc_move.
rewrite inv_id.
apply H.
rewrite cap_comm.
apply inc_def1.
apply H.
apply inc_def1.
rewrite -inv_inc_move.
rewrite inv_id.
apply H.
apply inc_antisym.
apply H0.
rewrite inv_inc_move.
apply H0.
Qed.

(* *)