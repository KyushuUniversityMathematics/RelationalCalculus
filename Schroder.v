Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Residual.
Require Import Logic.FunctionalExtensionality.

(** %
\section{Schr$\ddot{\mbox{o}}$der 圏の性質}
\begin{screen}
この節では, 特記が無い限り, 記号は以下の図式に従って割り振られるものとする.
$$
\xymatrix{
X \ar@{-_>}[r]^\alpha \ar@/^8mm/@{-_>}[rr]^\delta & Y \ar@{-_>}[r]_{\beta ,{\beta}', \beta_\lambda} & Z \ar@{-_>}[r]^\gamma & W \\
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

(** %
\begin{screen}
\begin{lemma}[schroder\_univalent2]
Let $\alpha$ be a univalent relation. Then,
$$
\alpha \cdot \beta^- = \alpha \cdot \nabla_{YZ} \sqcap (\alpha \cdot \beta)^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma schroder_univalent2 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 univalent_r alpha -> alpha ・ beta ^ = (alpha ・ ∇ Y Z) ∩ (alpha ・ beta) ^.
Proof.
move => H.
move : (@schroder_univalent1 _ _ _ alpha beta (∇ Y Z) H (@inc_alpha_universal _ _ _)) => H0.
rewrite cap_comm cap_universal in H0.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[schroder\_univalent3]
Let $\alpha$ be a univalent relation. Then,
$$
(\alpha \cdot \beta)^- = (\alpha \cdot \nabla_{YZ})^- \sqcup \alpha \cdot \beta^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma schroder_univalent3 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 univalent_r alpha -> (alpha ・ beta) ^ = (alpha ・ ∇ Y Z) ^ ∪ (alpha ・ beta ^).
Proof.
move => H.
rewrite (schroder_univalent2 H).
rewrite cup_cap_distr_l cup_comm complement_classic cap_comm cap_universal.
apply inc_def2.
apply rpc_inc_compat_r.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[schroder\_univalent4]
Let $\alpha$ be a univalent relation. Then,
$$
\alpha \rhd \beta = (\alpha \cdot \nabla_{YZ})^- \sqcup \alpha \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma schroder_univalent4 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 univalent_r alpha -> alpha △ beta = (alpha ・ ∇ Y Z) ^ ∪ (alpha ・ beta).
Proof.
move => H.
rewrite (residual_property9 H).
apply Logic.eq_sym.
apply cup_to_rpc.
Qed.

(** %
\begin{screen}
\begin{lemma}[schroder\_universal]
Let $\nabla_{XZ} \cdot \nabla_{ZW} = \nabla_{XW}$. Then,
$$
(\alpha \cdot \nabla_{YZ})^- \cdot \nabla_{ZW} = (\alpha \cdot \nabla_{YW})^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma schroder_universal {W X Y Z : eqType} {alpha : Rel X Y}:
 (∇ X Z ・ ∇ Z W) = ∇ X W ->
 (alpha ・ ∇ Y Z) ^ ・ ∇ Z W = (alpha ・ ∇ Y W) ^.
Proof.
move => H.
apply (@cap_cup_unique _ _ (alpha ・ ∇ Y W)).
rewrite cap_complement_empty cap_comm.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply (@inc_trans _ _ _ (((alpha ・ ∇ Y Z) ^ ∩ (alpha ・ ∇ Y Z)) ・ ∇ Z W)).
apply comp_inc_compat_ab_a'b.
apply cap_inc_compat_l.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
rewrite cap_comm cap_complement_empty comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
rewrite complement_classic.
apply inc_antisym.
apply inc_alpha_universal.
rewrite -H -(@complement_classic _ _ (alpha ・ ∇ Y Z)) comp_cup_distr_r.
apply cup_inc_compat_r.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_inv]
$$
(\alpha \rhd \beta)^\sharp = \beta^{- \sharp} \rhd \alpha^{- ^\sharp}.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_inv {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 (alpha △ beta) # = (beta ^) # △ (alpha ^) #.
Proof.
rewrite residual_to_complement residual_to_complement.
by [rewrite -inv_complement complement_invol inv_complement comp_inv].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_cupP\_distr\_l, residual\_cup\_distr\_l]
Let $\alpha$ be a univalent relation and $\exists \lambda , P(\lambda)$. Then,
$$
\alpha \rhd (\sqcup_{P(\lambda)} \beta_\lambda) = \sqcup_{P(\lambda)} (\alpha \rhd \beta_\lambda).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_cupP_distr_l
 {L X Y Z : eqType} {alpha : Rel X Y} {beta_L : L -> Rel Y Z} {P : L -> Prop}:
 univalent_r alpha -> (exists l : L, P l) ->
 alpha △ (∪_{P} beta_L) = ∪_{P} (fun l : L => alpha △ beta_L l).
Proof.
move => H.
elim => l H0.
rewrite (schroder_univalent4 H) comp_cupP_distr_l.
replace (∪_{P} (fun l : L => alpha △ beta_L l)) with (∪_{P} (fun l : L => (alpha ・ ∇ Y Z) ^ ∪ (alpha ・ beta_L l))).
apply (@cap_cup_unique _ _ (alpha ・ ∇ Y Z)).
rewrite cap_cup_distr_l cap_cupP_distr_l cap_complement_empty cup_comm cup_empty.
rewrite cap_cupP_distr_l.
apply f_equal.
apply functional_extensionality.
move => l0.
by [rewrite cap_cup_distr_l cap_complement_empty cup_comm cup_empty].
rewrite -cup_assoc complement_classic cup_comm cup_universal.
rewrite -(@complement_invol _ _ (alpha ・ ∇ Y Z)).
apply bool_lemma1.
rewrite complement_invol.
apply (@inc_trans _ _ _ ((alpha ・ ∇ Y Z) ^ ∪ (alpha ・ beta_L l))).
apply cup_l.
move : l H0.
apply inc_cupP.
apply inc_refl.
apply f_equal.
apply functional_extensionality.
move => l0.
by [rewrite (schroder_univalent4 H)].
Qed.

Lemma residual_cup_distr_l
 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 univalent_r alpha ->
 alpha △ (beta ∪ beta') = (alpha △ beta) ∪ (alpha △ beta').
Proof.
move => H.
rewrite cup_to_cupP cup_to_cupP.
rewrite (residual_cupP_distr_l H).
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
by [exists true].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_capP\_distr\_r, residual\_cap\_distr\_r]
Let $\exists \lambda , P(\lambda)$. Then,
$$
(\sqcap_{P(\lambda)} {\rho_\lambda}^\sharp) \rhd \rho = \sqcup_{P(\lambda)} ({\rho_\lambda}^\sharp \rhd \rho).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_capP_distr_r
 {L X : eqType} {rho : Rel i X} {rho_L : L -> Rel i X} {P : L -> Prop}:
 (exists l : L, P l) ->
 (∩_{P} (fun l : L => rho_L l #)) △ rho = ∪_{P} (fun l : L => rho_L l # △ rho).
Proof.
elim => l H.
rewrite residual_to_complement.
rewrite -(@complement_invol _ _ (∪_{P} (fun l0 : L => rho_L l0 # △ rho))).
apply f_equal.
rewrite de_morgan3.
replace (fun l0 : L => (rho_L l0 # △ rho) ^) with (fun l0 : L => rho_L l0 # ・ rho ^).
apply inc_antisym.
apply comp_capP_distr_r.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
apply (@inc_trans _ _ _ (((∩_{P} (fun l0 : L => rho_L l0 # ・ rho ^)) ・ (rho_L l # ・ rho ^) #) ・ (rho_L l # ・ rho ^))).
apply comp_inc_compat.
apply comp_inc_compat_ab_ab'.
move : l H.
apply inc_capP.
rewrite inv_capP_distr.
apply inc_refl.
move : l H.
apply inc_capP.
apply inc_refl.
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc.
apply (@inc_trans _ _ _ _ _ (comp_capP_distr_r)).
apply inc_capP.
move => l0 H0.
apply (@inc_trans _ _ _ ((rho_L l0 # ・ rho ^) ・ ((rho_L l # ・ rho ^) # ・ rho_L l #))).
move : l0 H0.
apply inc_capP.
apply inc_refl.
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
apply functional_extensionality.
move => l0.
by [rewrite residual_to_complement complement_invol].
Qed.