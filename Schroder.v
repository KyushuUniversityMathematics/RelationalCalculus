Require Import Basic_Notations_Set.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Residual.
Require Import Logic.FunctionalExtensionality.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Module Relation_Properties := Relation_Properties.main def.
Module Functions_Mappings := Functions_Mappings.main def.
Module Dedekind := Dedekind.main def.
Module Residual := Residual.main def.
Import Basic_Lemmas Relation_Properties Functions_Mappings Dedekind Residual.

(** %
\section{Schr$\ddot{\mbox{o}}$der 圏の性質}
\begin{screen}
この節では, 特記が無い限り, 記号は以下の図式に従って割り振られるものとする.
$$
\xymatrix{
X \ar@{-_>}[r]^\alpha \ar@/^8mm/@{-_>}[rr]^\delta & Y \ar@{-_>}[r]_{\beta ,{\beta}', \beta_\lambda} & Z \ar@{-_>}[r]^\gamma & W \\
I \ar@{-_>}[u]_{\rho} & & V \ar@{-_>}[u]_\tau & \\
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
Let $\alpha$ be a univalent relation, $f:(V \rel W) \to (Y \rel Z)$ and $\exists \beta , P(\beta)$. Then,
$$
\alpha \rhd (\sqcup_{P(\beta)} f(\beta)) = \sqcup_{P(\beta)} (\alpha \rhd f(\beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_cupP_distr_l {V W X Y Z : eqType}
 {alpha : Rel X Y} {f : Rel V W -> Rel Y Z} {P : Rel V W -> Prop}:
 univalent_r alpha -> (exists beta' : Rel V W, P beta') ->
 alpha △ (∪_{P} f) = ∪_{P} (fun beta : Rel V W => alpha △ f beta).
Proof.
move => H.
elim => beta' H0.
rewrite (schroder_univalent4 H) comp_cupP_distr_l.
replace (∪_{P} (fun beta : Rel V W => alpha △ f beta)) with (∪_{P} (fun beta : Rel V W => (alpha ・ ∇ Y Z) ^ ∪ (alpha ・ f beta))).
apply (@cap_cup_unique _ _ (alpha ・ ∇ Y Z)).
rewrite cap_cup_distr_l cap_cupP_distr_l cap_complement_empty cup_comm cup_empty.
rewrite cap_cupP_distr_l.
apply cupP_eq.
move => gamma H1.
by [rewrite cap_cup_distr_l cap_complement_empty cup_comm cup_empty].
rewrite -cup_assoc complement_classic cup_comm cup_universal.
rewrite -(@complement_invol _ _ (alpha ・ ∇ Y Z)).
apply bool_lemma1.
rewrite complement_invol.
apply (@inc_trans _ _ _ ((alpha ・ ∇ Y Z) ^ ∪ (alpha ・ f beta'))).
apply cup_l.
move : beta' H0.
apply inc_cupP.
apply inc_refl.
apply cupP_eq.
move => gamma H1.
by [rewrite (schroder_univalent4 H)].
Qed.

Lemma residual_cup_distr_l
 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 univalent_r alpha ->
 alpha △ (beta ∪ beta') = (alpha △ beta) ∪ (alpha △ beta').
Proof.
move => H.
rewrite cup_to_cupP (@cup_to_cupP _ _ _ _ _ _ id).
apply (residual_cupP_distr_l H).
exists beta.
by [left].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_capP\_distr\_r, residual\_cap\_distr\_r]
Let $f:(Y \rel Z) \to (I \rel X)$ and $\exists \alpha , P(\alpha)$. Then,
$$
(\sqcap_{P(\alpha)} f(\alpha)^\sharp) \rhd \rho = \sqcup_{P(\alpha)} (f(\alpha)^\sharp \rhd \rho).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_capP_distr_r
 {X Y Z : eqType} {rho : Rel i X} {f : Rel Y Z -> Rel i X} {P : Rel Y Z -> Prop}:
 (exists alpha' : Rel Y Z, P alpha') ->
 (∩_{P} (fun alpha : Rel Y Z => f alpha #)) △ rho = ∪_{P} (fun alpha : Rel Y Z => f alpha # △ rho).
Proof.
elim => alpha' H.
rewrite residual_to_complement.
rewrite -(@complement_invol _ _ (∪_{P} (fun alpha : Rel Y Z => f alpha # △ rho))).
apply f_equal.
rewrite de_morgan3.
replace (fun alpha : Rel Y Z => (f alpha # △ rho) ^) with (fun alpha : Rel Y Z => f alpha # ・ rho ^).
apply inc_antisym.
apply comp_capP_distr_r.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
apply (@inc_trans _ _ _ (((∩_{P} (fun alpha : Rel Y Z => f alpha # ・ rho ^)) ・ (f alpha' # ・ rho ^) #) ・ (f alpha' # ・ rho ^))).
apply comp_inc_compat.
apply comp_inc_compat_ab_ab'.
move : alpha' H.
apply inc_capP.
rewrite inv_capP_distr.
apply inc_refl.
move : alpha' H.
apply inc_capP.
apply inc_refl.
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc.
apply (@inc_trans _ _ _ _ _ (comp_capP_distr_r)).
apply inc_capP.
move => beta H0.
apply (@inc_trans _ _ _ ((f beta # ・ rho ^) ・ ((f alpha' # ・ rho ^) # ・ f alpha' #))).
move : beta H0.
apply inc_capP.
apply inc_refl.
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
apply functional_extensionality.
move => x.
by [rewrite residual_to_complement complement_invol].
Qed.

End main.