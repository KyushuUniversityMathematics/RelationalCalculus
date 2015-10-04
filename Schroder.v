Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Residual.

(** %
\section{Schr$\ddot{\mbox{o}}$der 圏の性質}
\begin{screen}
この節では, 特記が無い限り, 記号は以下の図式に従って割り振られるものとする.
$$
\xymatrix{
X \ar@{-_>}[r]^\alpha \ar@/^8mm/@{-_>}[rr]^\delta & Y \ar@{-_>}[r]^{\beta ,{\beta}'} & Z \ar@{-_>}[r]^\gamma & W \\
I \ar@{-_>}[u]_{\rho , \rho_\lambda} & & V \ar@{-_>}[u]_\tau & \\
}
$$
\end{screen}
% **)

(** %
\begin{screen}
\begin{lemma}[schroder\_equivalence1, schroder\_equivalence2]
$$
\alpha \cdot \beta \sqsubseteq \delta \Leftrightarrow \alpha^\sharp \cdot \delta^- \sqsubseteq \beta^- \Leftrightarrow \delta^- \cdot \beta^\sharp \sqsubseteq \alpha^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma schroder_equivalence1
 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {delta : Rel X Z}:
 (alpha ・ beta) ⊆ delta <-> (alpha # ・ delta ^) ⊆ beta ^.
Proof.
split; move => H.
rewrite bool_lemma2 complement_invol.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply bool_lemma2 in H.
rewrite cap_comm inv_invol H comp_empty_r.
apply inc_refl.
apply inc_empty_alpha.
rewrite bool_lemma2.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply bool_lemma2 in H.
rewrite cap_comm -(@complement_invol _ _ beta) H comp_empty_r.
apply inc_refl.
apply inc_empty_alpha.
Qed.

Lemma schroder_equivalence2
 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {delta : Rel X Z}:
 (alpha ・ beta) ⊆ delta <-> (delta ^ ・ beta #) ⊆ alpha ^.
Proof.
split; move => H.
rewrite bool_lemma2 complement_invol.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply bool_lemma2 in H.
rewrite cap_comm inv_invol H comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
rewrite bool_lemma2.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply bool_lemma2 in H.
rewrite cap_comm -(@complement_invol _ _ alpha) H comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_inv\_complement]
Let $\alpha$ and $\tau$ be functions. Then,
$$
(\alpha \cdot \beta \cdot \tau^\sharp)^- = \alpha \cdot \beta^- \cdot \tau^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_inv_complement
 {V X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {tau : Rel V Z}:
 function_r alpha -> function_r tau ->
 ((alpha ・ beta) ・ tau #) ^ = (alpha ・ beta ^) ・ tau #.
Proof.
move => H H0.
apply inc_antisym.
rewrite bool_lemma1 complement_invol.
apply inc_antisym.
rewrite -comp_cup_distr_r -comp_cup_distr_l complement_classic.
apply (@inc_trans _ _ _ (((alpha ・ alpha #) ・ ∇ X V) ・ (tau ・ tau #))).
apply (@inc_trans _ _ _ ((alpha ・ alpha #) ・ ∇ X V)).
apply comp_inc_compat_b_ab.
apply H.
apply comp_inc_compat_a_ab.
apply H0.
rewrite -comp_assoc (@comp_assoc _ _ _ _ alpha) (@comp_assoc _ _ _ _ alpha).
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
apply inc_alpha_universal.
rewrite bool_lemma2 complement_invol.
apply inc_antisym.
rewrite -(function_cap_distr H H0) cap_comm cap_complement_empty comp_empty_r comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[schroder\_univalent1]
Let $\alpha$ be a univalent relation and $\beta \sqsubseteq {\beta}'$. Then,
$$
\alpha \cdot ({\beta}' \sqcap \beta^-) = \alpha \cdot {\beta}' \sqcap (\alpha \cdot \beta)^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma schroder_univalent1
 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 univalent_r alpha -> beta ⊆ beta' ->
 alpha ・ (beta' ∩ beta ^) = (alpha ・ beta') ∩ (alpha ・ beta) ^.
Proof.
move => H H0.
apply (@cap_cup_unique _ _ (alpha ・ beta)).
replace ((alpha ・ beta) ∩ (alpha ・ (beta' ∩ beta ^))) with (φ X Z).
rewrite (@cap_comm _ _ (alpha ・ beta')) -cap_assoc.
by [rewrite cap_complement_empty cap_comm cap_empty].
apply inc_antisym.
apply inc_empty_alpha.
apply (@inc_trans _ _ _ ((alpha ・ beta) ∩ ((alpha ・ beta') ∩ (alpha ・ beta ^)))).
apply cap_inc_compat_l.
apply comp_cap_distr_l.
replace (φ X Z) with ((alpha ・ beta) ∩ (alpha ・ beta ^)).
apply cap_inc_compat_l.
apply cap_r.
apply inc_antisym.
move : (@univalent_residual _ _ _ _ beta H) => H1.
rewrite -inc_rpc.
rewrite residual_to_complement in H1.
apply H1.
apply inc_empty_alpha.
apply inc_def2 in H0.
rewrite -comp_cup_distr_l cup_cap_distr_l.
rewrite -H0 complement_classic cap_universal.
rewrite cup_cap_distr_l -comp_cup_distr_l.
by [rewrite -H0 complement_classic cap_universal].
Qed.

(* *)