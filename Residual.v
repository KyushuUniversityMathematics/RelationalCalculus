Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Domain.
Require Import Logic.FunctionalExtensionality.

(** %
\section{剰余合成関係の性質}
\subsection{基本的な性質}
\begin{screen}
\begin{lemma}[double\_residual]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\gamma :C \rel D$. Then
$$
\alpha \rhd (\beta \rhd \gamma) = (\alpha \cdot \beta) \rhd \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma double_residual
 {A B C D : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel C D}:
 alpha △ (beta △ gamma) = (alpha ・ beta) △ gamma.
Proof.
apply inc_lower.
move => delta.
split; move => H.
apply inc_residual.
rewrite comp_inv comp_assoc.
rewrite -inc_residual -inc_residual.
apply H.
rewrite inc_residual inc_residual.
rewrite -comp_assoc -comp_inv.
apply inc_residual.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_to\_complement]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then
$$
\alpha \rhd \beta = (\alpha \cdot \beta^-)^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_to_complement {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha △ beta = (alpha ・ beta ^) ^.
Proof.
apply inc_lower.
move => gamma.
split; move => H.
rewrite bool_lemma2 complement_invol cap_comm.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (@dedekind1 _ _ _ _ _ _)).
replace (beta ^ ∩ (alpha # ・ gamma)) with (φ B C).
rewrite comp_empty_r.
apply inc_refl.
apply Logic.eq_sym.
rewrite cap_comm.
apply bool_lemma2.
apply inc_residual.
apply H.
apply inc_empty_alpha.
apply inc_residual.
apply bool_lemma2.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (@dedekind1 _ _ _ _ _ _)).
rewrite inv_invol.
replace  (gamma ∩ (alpha ・ beta ^)) with (φ A C).
rewrite comp_empty_r.
apply inc_refl.
apply Logic.eq_sym.
rewrite -(@complement_invol _ _ (alpha ・ beta ^)).
apply bool_lemma2.
apply H.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_residual\_inc]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then
$$
\alpha^\sharp \cdot (\alpha \rhd \beta) \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_residual_inc {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha # ・ (alpha △ beta) ⊆ beta.
Proof.
apply inc_residual.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_residual\_inv]
Let $\alpha :A \rel B$ and $\gamma :A \rel C$. Then
$$
\gamma \sqsubseteq \alpha \rhd \alpha^\sharp \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_residual_inv {A B C : eqType} {alpha : Rel A B} {gamma : Rel A C}:
 gamma ⊆ (alpha △ (alpha # ・ gamma)).
Proof.
apply inc_residual.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[id\_inc\_residual]
Let $\alpha :A \rel B$. Then
$$
id_A \sqsubseteq \alpha \rhd \alpha^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma id_inc_residual {A B : eqType} {alpha : Rel A B}: Id A ⊆ (alpha △ alpha #).
Proof.
apply inc_residual.
rewrite comp_id_r.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_universal]
Let $\alpha :A \rel B$. Then
$$
\alpha \rhd \nabla_{BC} = \nabla_{AC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_universal {A B C : eqType} {alpha : Rel A B}: alpha △ ∇ B C = ∇ A C.
Proof.
apply inc_antisym.
apply inc_alpha_universal.
apply inc_residual.
apply inc_alpha_universal.
Qed.

(** %
\subsection{単調性と分配法則}
\begin{screen}
\begin{lemma}[residual\_inc\_compat]
Let $\alpha, {\alpha}' :A \rel B$ and $\beta, {\beta}' :B \rel C$. Then
$$
{\alpha}' \sqsubseteq \alpha \land \beta \sqsubseteq {\beta}' \Rightarrow \alpha \rhd \beta \sqsubseteq {\alpha}' \rhd {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_inc_compat
 {A B C : eqType} {alpha alpha' : Rel A B} {beta beta' : Rel B C}:
 alpha' ⊆ alpha -> beta ⊆ beta' -> (alpha △ beta) ⊆ (alpha' △ beta').
Proof.
move => H H0.
apply inc_residual.
apply (fun H' => @inc_trans _ _ _ _ _ H' H0).
move : (@inc_refl _ _ (alpha △ beta)) => H1.
apply inc_residual in H1.
apply (fun H' => @inc_trans _ _ _ _ _ H' H1).
apply comp_inc_compat_ab_a'b.
apply inc_inv.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_inc\_compat\_l]
Let $\alpha :A \rel B$ and $\beta, {\beta}' :B \rel C$. Then
$$
\beta \sqsubseteq {\beta}' \Rightarrow \alpha \rhd \beta \sqsubseteq \alpha \rhd {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_inc_compat_l
 {A B C : eqType} {alpha : Rel A B} {beta beta' : Rel B C}:
 beta ⊆ beta' -> (alpha △ beta) ⊆ (alpha △ beta').
Proof.
move => H.
apply (@residual_inc_compat _ _ _ _ _ _ _ (@inc_refl _ _ _) H).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_inc\_compat\_r]
Let $\alpha, {\alpha}' :A \rel B$ and $\beta :B \rel C$. Then
$$
{\alpha}' \sqsubseteq \alpha \Rightarrow \alpha \rhd \beta \sqsubseteq {\alpha}' \rhd \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_inc_compat_r
 {A B C : eqType} {alpha alpha' : Rel A B} {beta : Rel B C}:
 alpha' ⊆ alpha -> (alpha △ beta) ⊆ (alpha' △ beta).
Proof.
move => H.
apply (@residual_inc_compat _ _ _ _ _ _ _ H (@inc_refl _ _ _)).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_capL\_distr, residual\_cap\_distr]
Let $\alpha :A \rel B$ and $\beta_\lambda :B \rel C$. Then
$$
\alpha \rhd (\sqcap_{\lambda \in \Lambda} \beta_\lambda) = \sqcap_{\lambda \in \Lambda} (\alpha \rhd \beta_\lambda).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_capL_distr
 {A B C L : eqType} {alpha : Rel A B} {beta_L : L -> Rel B C}:
 alpha △ (∩_ beta_L) = ∩_ (fun l : L => alpha △ beta_L l).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capL.
move => l.
apply inc_residual.
move : l.
apply inc_capL.
apply inc_residual.
apply H.
apply inc_residual.
apply inc_capL.
move => l.
apply inc_residual.
move : l.
apply inc_capL.
apply H.
Qed.

Lemma residual_cap_distr
 {A B C : eqType} {alpha : Rel A B} {beta gamma : Rel B C}:
 alpha △ (beta ∩ gamma) = (alpha △ beta) ∩ (alpha △ gamma).
Proof.
rewrite cap_to_capL cap_to_capL.
rewrite residual_capL_distr.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_cupL\_distr, residual\_cup\_distr]
Let $\alpha_\lambda :A \rel B$ and $\beta :B \rel C$. Then
$$
(\sqcup_{\lambda \in \Lambda} \alpha_\lambda) \rhd \beta = \sqcap_{\lambda \in \Lambda} (\alpha_\lambda \rhd \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_cupL_distr
 {A B C L : eqType} {beta : Rel B C} {alpha_L : L -> Rel A B}:
 (∪_ alpha_L) △ beta = ∩_ (fun l : L => alpha_L l △ beta).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capL.
move => l.
apply inc_residual.
move : l.
apply inc_cupL.
rewrite -comp_cupL_distr_r -inv_cupL_distr.
apply inc_residual.
apply H.
apply inc_residual.
rewrite inv_cupL_distr comp_cupL_distr_r.
apply inc_cupL.
move => l.
apply inc_residual.
move : l.
apply inc_capL.
apply H.
Qed.

Lemma residual_cup_distr
 {A B C : eqType} {alpha beta : Rel A B} {gamma : Rel B C}:
 (alpha ∪ beta) △ gamma = (alpha △ gamma) ∩ (beta △ gamma).
Proof.
rewrite cup_to_cupL cap_to_capL.
rewrite residual_cupL_distr.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\subsection{剰余合成と関数}
\begin{screen}
\begin{lemma}[total\_residual]
Let $\alpha :A \to B$ be a total relation and $\beta :B \rel C$. Then
$$
\alpha \rhd \beta \sqsubseteq \alpha \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma total_residual {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 total_r alpha -> (alpha △ beta) ⊆ (alpha ・ beta).
Proof.
move => H.
apply (@inc_trans _ _ _ ((alpha ・ alpha #) ・ (alpha △ beta))).
apply (comp_inc_compat_b_ab H).
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inv_residual_inc.
Qed.

(** %
\begin{screen}
\begin{lemma}[univalent\_residual]
Let $\alpha :A \to B$ be a univalent relation and $\beta :B \rel C$. Then
$$
\alpha \cdot \beta \sqsubseteq \alpha \rhd \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma univalent_residual {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r alpha -> (alpha ・ beta) ⊆ (alpha △ beta).
Proof.
move => H.
apply (@inc_trans _ _ _ _ _ (@inc_residual_inv _ _ _ alpha _)).
apply residual_inc_compat_l.
rewrite -comp_assoc.
apply (comp_inc_compat_ab_b H).
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_residual1]
Let $\alpha :A \to B$ be a function and $\beta :B \rel C$. Then
$$
\alpha \rhd \beta = \alpha \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_residual1 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 function_r alpha -> alpha △ beta = alpha ・ beta.
Proof.
elim => H H0.
apply inc_antisym.
apply (total_residual H).
apply (univalent_residual H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_id]
Let $\alpha :A \to B$. Then
$$
id_A \rhd \alpha = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_id {A B : eqType} {alpha : Rel A B}:
 Id A △ alpha = alpha.
Proof.
move : (@function_residual1 _ _ _ (Id A) alpha (@id_function A)) => H.
rewrite comp_id_l in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[universal\_residual]
Let $\alpha :A \to B$. Then
$$
\nabla_{AA} \rhd \alpha \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma universal_residual {A B : eqType} {alpha : Rel A B}:
 ∇ A A △ alpha ⊆ alpha.
Proof.
apply (@inc_trans _ _ _ (Id A △ alpha)).
apply residual_inc_compat_r.
apply inc_alpha_universal.
rewrite residual_id.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_residual2]
Let $\alpha :A \to B$ be a function, $\beta :B \rel C$ and $\gamma :C \rel D$. Then
$$
\alpha \cdot (\beta \rhd \gamma) = (\alpha \cdot \beta) \rhd \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_residual2
 {A B C D : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel C D}:
 function_r alpha -> alpha ・ (beta △ gamma) = (alpha ・ beta) △ gamma.
Proof.
move => H.
rewrite -(@function_residual1 _ _ _ _ _ H).
apply double_residual.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_residual3]
Let $\alpha :A \rel B$, $\beta :B \rel C$ be relations and $\gamma :D \to C$ be a function. Then
$$
(\alpha \rhd \beta) \cdot \gamma^\sharp = \alpha \rhd (\beta \cdot \gamma^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma function_residual3
 {A B C D : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel D C}:
 function_r gamma -> (alpha △ beta) ・ gamma # = alpha △ (beta ・ gamma #).
Proof.
move => H.
apply inc_lower.
move => delta.
split; move => H0.
apply inc_residual.
rewrite -(@function_move2 _ _ _ _ _ _ H).
rewrite comp_assoc.
apply inc_residual.
rewrite (@function_move2 _ _ _ _ _ _ H).
apply H0.
rewrite -(@function_move2 _ _ _ _ _ _ H).
apply inc_residual.
rewrite -comp_assoc.
rewrite (@function_move2 _ _ _ _ _ _ H).
apply inc_residual.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_residual4]
Let $\alpha :A \rel B$, $\gamma :C \rel D$ be relations and $\beta :B \to C$ be a function. Then
$$
\alpha \cdot \beta \rhd \gamma = \alpha \rhd \beta \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_residual4
 {A B C D : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel C D}:
 function_r beta -> (alpha ・ beta) △ gamma = alpha △ (beta ・ gamma).
Proof.
move => H.
rewrite -double_residual.
by [rewrite (function_residual1 H)].
Qed.

(** %
\section{Galois 同値とその系}
\begin{screen}
\begin{lemma}[galois]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\gamma :A \rel C$. Then
$$
\gamma \sqsubseteq \alpha \rhd \beta \Leftrightarrow \alpha \sqsubseteq \gamma \rhd \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma galois {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 gamma ⊆ (alpha △ beta) <-> alpha ⊆ (gamma △ beta #).
Proof.
split; move => H.
apply inc_residual.
apply inv_inc_move.
rewrite comp_inv inv_invol.
apply inc_residual.
apply H.
apply inc_residual.
apply inv_inc_invol.
rewrite comp_inv inv_invol.
apply inc_residual.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[galois\_corollary1]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then
$$
\alpha \sqsubseteq (\alpha \rhd \beta) \rhd \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma galois_corollary1 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha ⊆ ((alpha △ beta) △ beta #).
Proof.
rewrite -galois.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[galois\_corollary2]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then
$$
((\alpha \rhd \beta) \rhd \beta^\sharp) \rhd \beta = \alpha \rhd \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma galois_corollary2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 ((alpha △ beta) △ beta #) △ beta = alpha △ beta.
Proof.
apply inc_antisym.
apply residual_inc_compat_r.
apply galois_corollary1.
move : (@galois_corollary1 _ _ _ (alpha △ beta) (beta #)) => H.
rewrite inv_invol in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[galois\_corollary3]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then
$$
\alpha = (\alpha \rhd \beta) \rhd \beta^\sharp \Leftrightarrow \exists \gamma :A \rel C, \alpha = \gamma \rhd \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma galois_corollary3 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha = (alpha △ beta) △ beta # <-> (exists gamma : Rel A C, alpha = gamma △ beta #).
Proof.
split; move => H.
exists (alpha △ beta).
apply H.
elim H => gamma H0.
rewrite H0.
move : (@galois_corollary2 _ _ _ gamma (beta #)) => H1.
rewrite inv_invol in H1.
by [rewrite H1].
Qed.

(** %
\section{その他の性質}
\begin{screen}
この節では, 特記が無い限り, 記号は以下の図式に従って割り振られるものとする.
$$
\xymatrix{
X \ar@{-_>}[r]^\alpha \ar@/^8mm/@{-_>}[rr]^\delta & Y \ar@{-_>}[r]^{\beta ,{\beta}'} \ar@{-_>}[d]^\eta & Z \ar@{-_>}[r]^\gamma & W \\
& V \ar@{-_>}[ru]_\tau & & \\
}
$$
\end{screen}
% **)

(** %
\begin{screen}
\begin{lemma}[residual\_property1]
$$
(\alpha \rhd \beta) \cdot \gamma \sqsubseteq \alpha \rhd \beta \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property1
 {W X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {gamma : Rel Z W}:
 ((alpha △ beta) ・ gamma) ⊆ (alpha △ (beta ・ gamma)).
Proof.
apply (@inc_trans _ _ _ (alpha △ (alpha # ・ ((alpha △ beta) ・ gamma)))).
apply inc_residual_inv.
apply residual_inc_compat_l.
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply inv_residual_inc.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property2]
$$
(\alpha \rhd \beta) \cdot (\beta^\sharp \rhd \eta) \sqsubseteq \alpha \rhd \eta.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property2
 {V X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {eta : Rel Y V}:
 ((alpha △ beta) ・ (beta # △ eta)) ⊆ (alpha △ eta).
Proof.
apply (@inc_trans _ _ _ _ _ (@residual_property1 _ _ _ _ _ _ _)).
apply residual_inc_compat_l.
move : (@inv_residual_inc _ _ _ (beta #) eta).
by [rewrite inv_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property3]
$$
\alpha \rhd \beta \sqsubseteq \alpha \cdot \eta \rhd \eta^\sharp \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property3
 {V X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {eta : Rel Y V}:
 (alpha △ beta) ⊆ ((alpha ・ eta) △ (eta # ・ beta)).
Proof.
apply (@inc_trans _ _ _ _ _ (@inc_residual_inv _ _ _ (alpha ・ eta) (alpha △ beta))).
apply residual_inc_compat_l.
rewrite comp_inv comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inv_residual_inc.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property4a, residual\_property4b]
$$
(\alpha \rhd \beta) \cdot \gamma \sqsubseteq (\alpha \rhd \beta \cdot \gamma) \sqcap \nabla_{XZ} \cdot \gamma \sqsubseteq (\alpha \rhd \beta \cdot \gamma) \cdot \gamma^\sharp \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property4a
 {W X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {gamma : Rel Z W}:
 ((alpha △ beta) ・ gamma) ⊆ ((alpha △ (beta ・ gamma)) ∩ (∇ X Z ・ gamma)).
Proof.
rewrite -(@cap_universal _ _ (alpha △ beta)).
apply (@inc_trans _ _ _ _ _ (@comp_cap_distr_r _ _ _ _ _ _)).
apply cap_inc_compat_r.
apply residual_property1.
Qed.

Lemma residual_property4b
 {W X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {gamma : Rel Z W}:
 ((alpha △ (beta ・ gamma)) ∩ (∇ X Z ・ gamma)) ⊆ ((alpha △ (beta ・ gamma)) ・ (gamma # ・ gamma)).
Proof.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (@dedekind2 _ _ _ _ _ _)).
rewrite cap_comm cap_universal comp_assoc.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property5]
Let $\tau$ be a univalent relation. Then,
$$
(\alpha \rhd \beta) \cdot \tau^\sharp = (\alpha \rhd \beta \cdot \tau^\sharp) \sqcap \nabla_{XZ} \cdot \tau^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property5
 {V X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {tau : Rel V Z}:
 univalent_r tau ->
 (alpha △ beta) ・ tau # = (alpha △ (beta ・ tau #)) ∩ (∇ X Z ・ tau #).
Proof.
move => H.
apply inc_antisym.
rewrite -(@cap_universal _ _ (alpha △ beta)).
apply (@inc_trans _ _ _ _ _ (@comp_cap_distr_r _ _ _ _ _ _)).
apply cap_inc_compat_r.
apply residual_property1.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (@dedekind2 _ _ _ _ _ _)).
rewrite cap_comm cap_universal inv_invol.
apply comp_inc_compat_ab_a'b.
apply (@inc_trans _ _ _ _ _ (@residual_property1 _ _ _ _ _ _ _)).
apply residual_inc_compat_l.
rewrite comp_assoc.
apply (comp_inc_compat_ab_a H).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property6]
$$
\alpha \rhd (\gamma^\sharp \rhd \beta^\sharp)^\sharp = (\gamma^\sharp \rhd (\alpha \rhd \beta)^\sharp)^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property6
 {W X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {gamma : Rel Z W}:
 alpha △ (gamma # △ beta #) # = (gamma # △ (alpha △ beta) #) #.
Proof.
apply inc_lower.
move => delta.
split; move => H.
apply inv_inc_move.
apply inc_residual.
apply inv_inc_move.
apply inc_residual.
rewrite -comp_inv comp_assoc.
apply inv_inc_move.
apply inc_residual.
apply inv_inc_invol.
rewrite comp_inv inv_invol.
apply inc_residual.
apply H.
apply inc_residual.
apply inv_inc_move.
apply inc_residual.
apply inv_inc_move.
rewrite comp_inv inv_invol inv_invol comp_assoc.
apply inc_residual.
apply inv_inc_invol.
rewrite comp_inv.
apply inc_residual.
apply inv_inc_move.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property7a, residual\_property7b]
$$
\alpha \rhd (\beta \Rightarrow {\beta}') \sqsubseteq (\alpha \cdot \beta \Rightarrow \alpha \cdot {\beta}') \sqsubseteq \alpha \rhd (\beta \Rightarrow \alpha^\sharp \cdot \alpha \cdot {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property7a
 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 (alpha △ (beta >> beta')) ⊆ ((alpha ・ beta) >> (alpha ・ beta')).
Proof.
apply inc_rpc.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (@dedekind1 _ _ _ _ _ _)).
apply comp_inc_compat_ab_ab'.
rewrite cap_comm.
apply inc_rpc.
apply inv_residual_inc.
Qed.

Lemma residual_property7b
 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 ((alpha ・ beta) >> (alpha ・ beta')) ⊆ (alpha △ (beta >> (alpha # ・ (alpha ・ beta')))).
Proof.
rewrite inc_residual inc_rpc.
apply (@inc_trans _ _ _ _ _ (@dedekind1 _ _ _ _ _ _)).
apply comp_inc_compat_ab_ab'.
rewrite inv_invol -inc_rpc.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property8]
Let $\alpha$ be a univalent relation. Then,
$$
\alpha \rhd (\beta \Rightarrow {\beta}') = (\alpha \cdot \beta \Rightarrow \alpha \cdot {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property8
 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 univalent_r alpha -> alpha △ (beta >> beta') = (alpha ・ beta) >> (alpha ・ beta').
Proof.
move => H.
apply inc_antisym.
apply residual_property7a.
apply (@inc_trans _ _ _ _ _ residual_property7b).
apply residual_inc_compat_l.
apply rpc_inc_compat_l.
rewrite -comp_assoc.
apply (comp_inc_compat_ab_b H).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property9]
Let $\alpha$ be a univalent relation. Then,
$$
\alpha \rhd \beta = (\alpha \cdot \nabla_{YZ} \Rightarrow \alpha \cdot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property9
 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 univalent_r alpha -> alpha △ beta = (alpha ・ ∇ Y Z) >> (alpha ・ beta).
Proof.
move => H.
by [rewrite -(residual_property8 H) rpc_universal_alpha].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property10]
Let $\alpha$ be a univalent relation. Then,
$$
\alpha \cdot \beta = \domain{\alpha} \cdot (\alpha \rhd \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property10
 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 univalent_r alpha -> alpha ・ beta = domain alpha ・ (alpha △ beta).
Proof.
move => H.
apply inc_antisym.
replace (alpha ・ beta) with (domain alpha ・ (alpha ・ beta)).
apply comp_inc_compat_ab_ab'.
rewrite inc_residual -comp_assoc.
apply (comp_inc_compat_ab_b H).
by [rewrite -comp_assoc domain_comp_alpha1].
apply (@inc_trans _ _ _ ((alpha ・ alpha #) ・ (alpha △ beta))).
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inv_residual_inc.
Qed.

(* *)