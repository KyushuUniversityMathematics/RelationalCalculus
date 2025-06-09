Require Import MyLib.Basic_Notations_Set.
Require Import MyLib.Basic_Lemmas.
Require Import MyLib.Relation_Properties.
Require Import MyLib.Functions_Mappings.
Require Import MyLib.Dedekind.
Require Import MyLib.Tactics.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Module Relation_Properties := Relation_Properties.main def.
Module Functions_Mappings := Functions_Mappings.main def.
Module Dedekind := Dedekind.main def.
Module Tactics := Tactics.main def.
Import Basic_Lemmas Relation_Properties Functions_Mappings Dedekind Tactics.

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

End main.