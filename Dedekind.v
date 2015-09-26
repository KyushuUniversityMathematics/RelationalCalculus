Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.

(** %
\section{Dedekind formula に関する補題}
\begin{screen}
\begin{lemma}[dedekind1]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\gamma :A \rel C$. Then
$$
\alpha \cdot \beta \sqcap \gamma \sqsubseteq \alpha \cdot (\beta \sqcap \alpha^\sharp \cdot \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind1
 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 ((alpha ・ beta) ∩ gamma) ⊆ (alpha ・ (beta ∩ (alpha # ・ gamma))).
Proof.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _ )).
apply comp_inc_compat_ab_a'b.
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[dedekind2]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\gamma :A \rel C$. Then
$$
\alpha \cdot \beta \sqcap \gamma \sqsubseteq (\alpha \sqcap \gamma \cdot \beta^\sharp) \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind2
 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 ((alpha ・ beta) ∩ gamma) ⊆ ((alpha ∩ (gamma ・ beta #)) ・ beta).
Proof.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _ )).
apply comp_inc_compat_ab_ab'.
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[relation\_rel\_inv\_rel]
Let $\alpha :A \rel B$. Then
$$
\alpha \sqsubseteq \alpha \cdot \alpha^\sharp \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma relation_rel_inv_rel {A B : eqType} {alpha : Rel A B}:
 alpha ⊆ ((alpha ・ alpha #) ・ alpha).
Proof.
move : (@dedekind1 _ _ _ alpha (Id B) alpha) => H.
rewrite comp_id_r cap_idem in H.
apply (@inc_trans _ _ _ _ _ H).
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply cap_r.
Qed.

(** %
\section{Dedekind formula と全関係}
\begin{screen}
\begin{lemma}[dedekind\_universal1]
Let $\alpha :B \rel C$. Then
$$
\nabla_{AC} \cdot \alpha^\sharp \cdot \alpha = \nabla_{AB} \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_universal1 {A B C : eqType} {alpha : Rel B C}:
 (∇ A C ・ alpha #) ・ alpha = ∇ A B ・ alpha.
Proof.
apply inc_antisym.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ (∇ A B ・ ((alpha ・ alpha #) ・ alpha))).
apply comp_inc_compat_ab_ab'.
apply relation_rel_inv_rel.
rewrite -comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma} {\bf (dedekind\_universal2a, dedekind\_universal2b, \\
dedekind\_universal2c)}
Let $\alpha :A \rel B$ and $\beta :C \rel B$. Then
$$
\nabla_{IC} \cdot \beta \sqsubseteq \nabla_{IA} \cdot \alpha \Leftrightarrow \nabla_{CC} \cdot \beta \sqsubseteq \nabla_{CA} \cdot \alpha \Leftrightarrow \beta \sqsubseteq \beta \cdot \alpha^\sharp \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_universal2a {A B C : eqType} {alpha : Rel A B} {beta : Rel C B}:
 (∇ i C ・ beta) ⊆ (∇ i A ・ alpha) -> (∇ C C ・ beta) ⊆ (∇ C A ・ alpha).
Proof.
move => H.
rewrite -unit_universal -(@lemma_for_tarski2 C A).
rewrite comp_assoc comp_assoc.
apply (comp_inc_compat_ab_ab' H).
Qed.

Lemma dedekind_universal2b {A B C : eqType} {alpha : Rel A B} {beta : Rel C B}:
 (∇ C C ・ beta) ⊆ (∇ C A ・ alpha) -> beta ⊆ ((beta ・ alpha #) ・ alpha).
Proof.
move => H.
apply (@inc_trans _ _ _ (beta ∩ (∇ C C ・ beta))).
apply inc_cap.
split.
apply inc_refl.
apply comp_inc_compat_b_ab.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ (beta ∩ (∇ C A ・ alpha))).
apply (cap_inc_compat_l H).
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (@dedekind2 _ _ _ _ _ _)).
apply comp_inc_compat_ab_a'b.
apply cap_r.
Qed.

Lemma dedekind_universal2c {A B C : eqType} {alpha : Rel A B} {beta : Rel C B}:
 beta ⊆ ((beta ・ alpha #) ・ alpha) -> (∇ i C ・ beta) ⊆ (∇ i A ・ alpha).
Proof.
move => H.
apply (@inc_trans _ _ _ (∇ i C ・ ((beta ・ alpha #) ・ alpha))).
apply (comp_inc_compat_ab_ab' H).
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[dedekind\_universal3a, dedekind\_universal3b]
Let $\alpha :A \rel B$ and $\beta :A \rel C$. Then
$$
\beta \cdot \nabla_{CI} \sqsubseteq \alpha \cdot \nabla_{BI} \Leftrightarrow \beta \cdot \nabla_{CC} \sqsubseteq \alpha \cdot \nabla_{BC} \Leftrightarrow \beta \sqsubseteq \alpha \cdot \alpha^\sharp \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_universal3a {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 (beta ・ ∇ C i) ⊆ (alpha ・ ∇ B i) <-> (beta ・ ∇ C C) ⊆ (alpha ・ ∇ B C).
Proof.
split; move => H.
apply inv_inc_invol.
rewrite comp_inv comp_inv inv_universal inv_universal.
apply dedekind_universal2a.
apply inv_inc_invol.
rewrite comp_inv comp_inv inv_invol inv_invol inv_universal inv_universal.
apply H.
apply inv_inc_invol.
rewrite comp_inv comp_inv inv_universal inv_universal.
apply dedekind_universal2c.
apply dedekind_universal2b.
apply inv_inc_invol.
rewrite comp_inv comp_inv inv_invol inv_invol inv_universal inv_universal.
apply H.
Qed.

Lemma dedekind_universal3b {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 (beta ・ ∇ C i) ⊆ (alpha ・ ∇ B i) <-> beta ⊆ ((alpha ・ alpha #) ・ beta).
Proof.
split; move => H.
apply inv_inc_invol.
rewrite comp_inv comp_inv -comp_assoc.
apply dedekind_universal2b.
apply dedekind_universal2a.
apply inv_inc_invol.
rewrite comp_inv comp_inv inv_invol inv_invol inv_universal inv_universal.
apply H.
apply inv_inc_invol.
rewrite comp_inv comp_inv inv_universal inv_universal.
apply dedekind_universal2c.
rewrite -comp_inv -comp_inv -comp_assoc.
apply inc_inv.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[universal\_total]
Let $\alpha :A \rel B$. Then
$$
\alpha \cdot \nabla_{BI} = \nabla_{AI} \Leftrightarrow \mbox{``$\alpha$ is total''}.
$$
\end{lemma}
\end{screen}
% **)
Lemma universal_total {A B : eqType} {alpha : Rel A B}:
 alpha ・ ∇ B i = ∇ A i <-> total_r alpha.
Proof.
move : (@dedekind_universal3b _ _ _ alpha (Id A)) => H.
rewrite comp_id_l comp_id_r in H.
rewrite /total_r.
rewrite -H.
split; move => H0.
rewrite H0.
apply inc_refl.
apply inc_antisym.
apply inc_alpha_universal.
apply H0.
Qed.

(** %
\section{Dedekind formula と恒等関係}
\begin{screen}
\begin{lemma}[dedekind\_id1]
Let $\alpha :A \rel A$. Then
$$
\alpha \sqsubseteq id_A \Rightarrow \alpha^\sharp = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_id1 {A : eqType} {alpha : Rel A A}: alpha ⊆ Id A -> alpha # = alpha.
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
apply inv_inc_move.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[dedekind\_id2]
Let $\alpha :A \rel A$. Then
$$
\alpha \sqsubseteq id_A \Rightarrow \alpha \cdot \alpha = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_id2 {A : eqType} {alpha : Rel A A}:
 alpha ⊆ Id A -> alpha ・ alpha = alpha.
Proof.
move => H.
apply inc_antisym.
apply (comp_inc_compat_ab_a H).
move : (dedekind_id1 H) => H0.
apply (@inc_trans _ _ _ ((alpha ・ Id A) ∩ Id A)).
rewrite comp_id_r.
apply inc_cap.
split.
apply inc_refl.
apply H.
apply (@inc_trans _ _ _ _ _ (@dedekind1 _ _ _ _ _ _)).
apply comp_inc_compat_ab_ab'.
rewrite H0 comp_id_r.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[dedekind\_id3]
Let $\alpha, \beta :A \rel A$. Then
$$
\alpha \sqsubseteq id_A \land \beta \sqsubseteq id_A \Rightarrow \alpha \cdot \beta = \alpha \sqcap \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_id3 {A : eqType} {alpha beta : Rel A A}:
 alpha ⊆ Id A -> beta ⊆ Id A -> alpha ・ beta = alpha ∩ beta.
Proof.
move => H H0.
apply inc_antisym.
apply inc_cap.
split.
apply (comp_inc_compat_ab_a H0).
apply (comp_inc_compat_ab_b H).
replace (alpha ∩ beta) with ((alpha ∩ beta) ・ (alpha ∩ beta)).
apply comp_inc_compat.
apply cap_l.
apply cap_r.
apply dedekind_id2.
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[dedekind\_id4]
Let $\alpha, \beta :A \rel A$. Then
$$
\alpha \sqsubseteq id_A \land \beta \sqsubseteq id_A \Rightarrow (\alpha \rhd \beta) \sqcap id_A = (\alpha \Rightarrow \beta) \sqcap id_A.
$$
\end{lemma}
\end{screen}
% **)
Lemma dedekind_id4 {A : eqType} {alpha beta : Rel A A}:
 alpha ⊆ Id A -> beta ⊆ Id A -> (alpha △ beta) ∩ Id A = (alpha >> beta) ∩ Id A.
Proof.
move => H H0.
apply inc_lower.
move => gamma.
rewrite inc_cap inc_cap.
split; elim => H1 H2.
split.
rewrite inc_rpc cap_comm.
rewrite -(@dedekind_id3 _ _ _ H H2).
rewrite -(@dedekind_id1 _ _ H).
apply inc_residual.
apply H1.
apply H2.
split.
rewrite inc_residual (@dedekind_id1 _ _ H) (@dedekind_id3 _ _ _ H H2).
rewrite cap_comm -inc_rpc.
apply H1.
apply H2.
Qed.