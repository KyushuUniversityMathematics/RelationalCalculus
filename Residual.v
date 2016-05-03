Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Domain.
Require Import Logic.FunctionalExtensionality.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Module Relation_Properties := Relation_Properties.main def.
Module Functions_Mappings := Functions_Mappings.main def.
Module Dedekind := Dedekind.main def.
Module Domain := Domain.main def.
Import Basic_Lemmas Relation_Properties Functions_Mappings Dedekind Domain.

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
apply (@inc_trans _ _ _ _ _ (dedekind1)).
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
apply (@inc_trans _ _ _ _ _ (dedekind1)).
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
\begin{lemma}[residual\_capP\_distr\_l, residual\_cap\_distr\_l]
Let $\alpha :A \rel B$, $f:(D \rel E) \to (B \rel C)$ and $P$ : predicate. Then
$$
\alpha \rhd (\sqcap_{P(\beta)} f(\beta)) = \sqcap_{P(\beta)} (\alpha \rhd f(\beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_capP_distr_l {A B C D E : eqType}
 {alpha : Rel A B} {f : Rel D E -> Rel B C} {P : Rel D E -> Prop}:
 alpha △ (∩_{P} f) = ∩_{P} (fun beta : Rel D E => alpha △ f beta).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capP.
move => beta H0.
apply inc_residual.
move : beta H0.
apply inc_capP.
apply inc_residual.
apply H.
apply inc_residual.
apply inc_capP.
move => beta H0.
apply inc_residual.
move : beta H0.
apply inc_capP.
apply H.
Qed.

Lemma residual_cap_distr_l
 {A B C : eqType} {alpha : Rel A B} {beta gamma : Rel B C}:
 alpha △ (beta ∩ gamma) = (alpha △ beta) ∩ (alpha △ gamma).
Proof.
rewrite cap_to_capP (@cap_to_capP _ _ _ _ _ _ id).
apply residual_capP_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_cupP\_distr\_r, residual\_cup\_distr\_r]
Let $f:(D \rel E) \to (A \rel B)$, $\beta :B \rel C$ and $P$ : predicate. Then
$$
(\sqcup_{P(\alpha)} f(\alpha)) \rhd \beta = \sqcap_{P(\alpha)} (f(\alpha) \rhd \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_cupP_distr_r {A B C D E : eqType}
 {beta : Rel B C} {f : Rel D E -> Rel A B} {P : Rel D E -> Prop}:
 (∪_{P} f) △ beta = ∩_{P} (fun alpha : Rel D E => f alpha △ beta).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capP.
move => alpha H0.
apply inc_residual.
move : alpha H0.
apply inc_cupP.
rewrite -comp_cupP_distr_r -inv_cupP_distr.
apply inc_residual.
apply H.
apply inc_residual.
rewrite inv_cupP_distr comp_cupP_distr_r.
apply inc_cupP.
move => alpha H0.
apply inc_residual.
move : alpha H0.
apply inc_capP.
apply H.
Qed.

Lemma residual_cup_distr_r
 {A B C : eqType} {alpha beta : Rel A B} {gamma : Rel B C}:
 (alpha ∪ beta) △ gamma = (alpha △ gamma) ∩ (beta △ gamma).
Proof.
rewrite (@cup_to_cupP _ _ _ _ _ _ id) (@cap_to_capP _ _ _ _ _ _ (fun x => x △ gamma)).
apply residual_cupP_distr_r.
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
Let $\alpha :A \rel B$. Then
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
apply (@inc_trans _ _ _ _ _ (residual_property1)).
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
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply cap_inc_compat_r.
apply residual_property1.
Qed.

Lemma residual_property4b
 {W X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {gamma : Rel Z W}:
 ((alpha △ (beta ・ gamma)) ∩ (∇ X Z ・ gamma)) ⊆ ((alpha △ (beta ・ gamma)) ・ (gamma # ・ gamma)).
Proof.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
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
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply cap_inc_compat_r.
apply residual_property1.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
rewrite cap_comm cap_universal inv_invol.
apply comp_inc_compat_ab_a'b.
apply (@inc_trans _ _ _ _ _ (residual_property1)).
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
Lemma residual_property7a {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 (alpha △ (beta >> beta')) ⊆ ((alpha ・ beta) >> (alpha ・ beta')).
Proof.
apply inc_rpc.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
rewrite cap_comm.
apply inc_rpc.
apply inv_residual_inc.
Qed.

Lemma residual_property7b {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
 ((alpha ・ beta) >> (alpha ・ beta')) ⊆ (alpha △ (beta >> (alpha # ・ (alpha ・ beta')))).
Proof.
rewrite inc_residual inc_rpc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
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
Lemma residual_property8 {X Y Z : eqType} {alpha : Rel X Y} {beta beta' : Rel Y Z}:
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
Lemma residual_property9 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
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
Lemma residual_property10 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
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

(** %
\begin{screen}
\begin{lemma}[residual\_property11]
$$
(\alpha \cdot \beta \Rightarrow \delta) \sqsubseteq \alpha \rhd (\beta \Rightarrow \alpha^\sharp \cdot \delta).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property11
 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z} {delta : Rel X Z}:
 ((alpha ・ beta) >> delta) ⊆ (alpha △ (beta >> (alpha # ・ delta))).
Proof.
apply inc_residual.
apply inc_rpc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
rewrite inv_invol.
apply comp_inc_compat_ab_ab'.
apply inc_rpc.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property12a, residual\_property12b]
Let $u \sqsubseteq id_X$. Then,
$$
u \rhd \alpha = u \cdot \nabla_{XY} \Rightarrow \alpha = u \rhd u \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property12a {X Y : eqType} {u : Rel X X} {alpha : Rel X Y}:
 u ⊆ Id X -> u △ alpha = (u ・ ∇ X Y) >> alpha.
Proof.
move => H.
apply inc_antisym.
assert (univalent_r u).
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
apply comp_inc_compat_ab_b.
rewrite -inv_id.
apply (@inc_inv _ _ _ _ H).
rewrite (residual_property9 H0).
apply rpc_inc_compat_l.
apply (comp_inc_compat_ab_b H).
apply (@inc_trans _ _ _ _ _ residual_property11).
apply residual_inc_compat_l.
rewrite rpc_universal_alpha.
apply comp_inc_compat_ab_b.
rewrite -inv_id.
apply (@inc_inv _ _ _ _ H).
Qed.

Lemma residual_property12b {X Y : eqType} {u : Rel X X} {alpha : Rel X Y}:
 u ⊆ Id X -> u △ alpha = u △ (u ・ alpha).
Proof.
move => H.
apply inc_antisym.
rewrite (residual_property12a H).
apply (@inc_trans _ _ _ _ _ residual_property11).
apply residual_inc_compat_l.
rewrite rpc_universal_alpha.
apply comp_inc_compat_ab_a'b.
rewrite (dedekind_id1 H).
apply inc_refl.
apply residual_inc_compat_l.
apply (comp_inc_compat_ab_b H).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property13]
$$
(\alpha \cdot \nabla_{YZ} \sqcap \delta) \rhd \gamma = (\alpha \cdot \nabla_{YW} \Rightarrow (\delta \rhd \gamma)).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property13
 {W X Y Z : eqType} {alpha : Rel X Y} {gamma : Rel Z W} {delta : Rel X Z}:
 ((alpha ・ ∇ Y Z) ∩ delta) △ gamma = (alpha ・ ∇ Y W) >> (delta △ gamma).
Proof.
apply inc_antisym.
rewrite inc_rpc inc_residual.
remember (((alpha ・ ∇ Y Z) ∩ delta) △ gamma) as sigma1.
apply (@inc_trans _ _ _ (((alpha ・ ∇ Y Z) ∩ delta) # ・ sigma1)).
apply (@inc_trans _ _ _ (((alpha ・ ∇ Y Z) ∩ delta) # ・ (sigma1 ∩ (alpha ・ ∇ Y W)))).
assert ((delta # ・ (sigma1 ∩ (alpha ・ ∇ Y W))) ⊆ (delta # ・ sigma1)).
apply comp_inc_compat_ab_ab'.
apply cap_l.
apply inc_def1 in H.
rewrite H.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply comp_inc_compat_ab_a'b.
rewrite (@inv_cap_distr _ _ _ delta) cap_comm.
apply cap_inc_compat_r.
rewrite inv_cap_distr.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply (@inc_trans _ _ _ _ _ (cap_r)).
rewrite comp_inv comp_inv -comp_assoc (@inv_universal Y Z).
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
apply comp_inc_compat_ab_ab'.
apply cap_l.
rewrite Heqsigma1.
apply inc_residual.
apply inc_refl.
rewrite inc_residual.
remember ((alpha ・ ∇ Y W) >> (delta △ gamma)) as sigma2.
apply (@inc_trans _ _ _ (delta # ・ ((alpha ・ ∇ Y W) ∩ sigma2))).
apply (@inc_trans _ _ _ (((alpha ・ ∇ Y Z) ∩ delta) # ・ ((alpha ・ ∇ Y W) ∩ sigma2))).
assert ((((alpha ・ ∇ Y Z) ∩ delta) # ・ sigma2) ⊆ (delta # ・ sigma2)).
apply comp_inc_compat_ab_a'b.
apply inc_inv.
apply cap_r.
apply inc_def1 in H.
rewrite H.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
rewrite cap_comm inv_invol.
apply cap_inc_compat_r.
apply (@inc_trans _ _ _ ((alpha ・ ∇ Y Z) ・ (delta # ・ sigma2))).
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
apply comp_inc_compat_ab_a'b.
apply inc_inv.
apply cap_r.
rewrite Heqsigma2.
rewrite -inc_residual cap_comm -inc_rpc.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property14]
Let $\nabla_{XX} \cdot \alpha \sqsubseteq \alpha$. Then,
$$
\nabla_{XX} \cdot (\alpha \rhd \beta) \sqsubseteq \alpha \rhd \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property14 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 (∇ X X ・ alpha) ⊆ alpha -> (∇ X X ・ (alpha △ beta)) ⊆ (alpha △ beta).
Proof.
move => H.
apply (@inc_trans _ _ _ (∇ X X ・ (∇ X X △ (alpha △ beta)))).
apply comp_inc_compat_ab_ab'.
rewrite double_residual.
apply (residual_inc_compat_r H).
rewrite -inv_universal -inc_residual inv_universal.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property15]
Let $\beta \cdot \nabla_{ZZ} \sqsubseteq \beta$. Then,
$$
(\alpha \rhd \beta) \cdot \nabla_{ZZ} \sqsubseteq \alpha \rhd \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property15 {X Y Z : eqType} {alpha : Rel X Y} {beta : Rel Y Z}:
 (beta ・ ∇ Z Z) ⊆ beta -> ((alpha △ beta) ・ ∇ Z Z) ⊆ (alpha △ beta).
Proof.
move => H.
apply (@inc_trans _ _ _ _ _ (residual_property1)).
apply (residual_inc_compat_l H).
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property16]
$$
id_X \sqsubseteq \alpha \rhd \alpha^\sharp \land (\alpha \rhd \alpha^\sharp) \cdot (\alpha \rhd \alpha^\sharp) \sqsubseteq \alpha \rhd \alpha^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property16 {X Y : eqType} {alpha : Rel X Y}:
 Id X ⊆ (alpha △ alpha #) /\
 ((alpha △ alpha #) ・ (alpha △ alpha #)) ⊆ (alpha △ alpha #).
Proof.
split.
rewrite inc_residual comp_id_r.
apply inc_refl.
move : (@residual_property2 _ _ _ _ alpha (alpha #) (alpha #)) => H.
rewrite inv_invol in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_property17]
Let $P(y):=$ ``$y :I \rel Y$ is a function''. Then,
$$
\sqcup_{P(y)} y^\sharp \cdot y = id_Y \Rightarrow \alpha \rhd \beta = \sqcap_{P(y)} (\alpha \cdot y^\sharp \cdot \nabla_{IZ} \Rightarrow \alpha \cdot y^\sharp \cdot y \cdot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_property17 {X Y Z : eqType}
 {alpha : Rel X Y} {beta : Rel Y Z} {P : Rel i Y -> Prop}:
 P = (fun y : Rel i Y => function_r y) ->
 ∪_{P} (fun y : Rel i Y => y # ・ y) = Id Y ->
 alpha △ beta = ∩_{P} (fun y : Rel i Y =>
  ((alpha ・ y #) ・ ∇ i Z) >> ((alpha ・ y #) ・ (y ・ beta))).
Proof.
move => H H0.
replace (alpha △ beta) with ((alpha ・ Id Y) △ beta).
rewrite -H0 comp_cupP_distr_l residual_cupP_distr_r.
apply capP_eq.
move => y H1.
rewrite H in H1.
rewrite -comp_assoc (function_residual4 H1).
apply residual_property9.
rewrite /univalent_r.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
by [rewrite comp_id_r].
Qed.

(** %
\section{順序の関係と左剰余合成}
\subsection{max, sup, min, inf}
\begin{screen}
$\xi : X \rel X$ を集合 $X$ における順序と見なしたときの, 関係 $\rho : V \rel X$ の 最大値(max), 上限(sup), 最小値(min), 下限(inf)はそれぞれ, 以下のように定義される.
\begin{itemize}
\item $max(\rho , \xi):= \rho \sqcap (\rho \rhd \xi)$
\item $sup(\rho , \xi):= (\rho \rhd \xi) \sqcap ((\rho \rhd \xi) \rhd \xi^\sharp)$
\item $min(\rho , \xi):= \rho \sqcap (\rho \rhd \xi^\sharp) (= max(\rho , \xi^\sharp))$
\item $inf(\rho , \xi):= (\rho \rhd \xi^\sharp) \sqcap ((\rho \rhd \xi^\sharp) \rhd \xi) (= sup(\rho , \xi^\sharp))$
\end{itemize}
\end{screen}
% **)
Definition max {V X : eqType} (rho : Rel V X) (xi : Rel X X)
 := rho ∩ (rho △ xi).
Definition sup {V X : eqType} (rho : Rel V X) (xi : Rel X X)
 := (rho △ xi) ∩ ((rho △ xi) △ xi #).
Definition min {V X : eqType} (rho : Rel V X) (xi : Rel X X)
 := rho ∩ (rho △ xi #).
Definition inf {V X : eqType} (rho : Rel V X) (xi : Rel X X)
 := (rho △ xi #) ∩ ((rho △ xi #) △ xi).

(** %
\begin{screen}
\begin{lemma}[max\_inc\_sup]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
max(\rho , \xi) \sqsubseteq sup(\rho , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma max_inc_sup {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 max rho xi ⊆ sup rho xi.
Proof.
rewrite /max/sup.
rewrite cap_comm.
apply cap_inc_compat_l.
apply galois_corollary1.
Qed.

(** %
\begin{screen}
\begin{lemma}[min\_inc\_inf]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
min(\rho , \xi) \sqsubseteq inf(\rho , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma min_inc_inf {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 min rho xi ⊆ inf rho xi.
Proof.
rewrite /min/inf.
rewrite cap_comm.
apply cap_inc_compat_l.
move : (@galois_corollary1 _ _ _ rho (xi #)) => H.
rewrite inv_invol in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inf\_to\_sup]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
inf(\rho , \xi) = sup(\rho \rhd \xi^\sharp , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma inf_to_sup {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 inf rho xi = sup (rho △ xi #) xi.
Proof.
rewrite /sup/inf.
rewrite cap_comm.
move : (@galois_corollary2 _ _ _ rho (xi #)) => H.
rewrite inv_invol in H.
by [rewrite H].
Qed.

(** %
\begin{screen}
\begin{lemma}[sup\_to\_inf]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
sup(\rho , \xi) = inf(\rho \rhd \xi , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma sup_to_inf {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 sup rho xi = inf (rho △ xi) xi.
Proof.
rewrite /sup/inf.
rewrite cap_comm.
by [rewrite galois_corollary2].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_inc\_sup1, residual\_inc\_sup2]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
sup(\rho , \xi) \sqsubseteq \rho \rhd \xi \sqsubseteq sup(\rho , \xi) \rhd \xi.
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_inc_sup1 {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 sup rho xi ⊆ (rho △ xi).
Proof.
apply cap_l.
Qed.

Lemma residual_inc_sup2 {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 (rho △ xi) ⊆ ((sup rho xi) △ xi).
Proof.
rewrite galois.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[max\_inc\_xi\_cap]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
(max(\rho , \xi))^\sharp \cdot max(\rho , \xi) \sqsubseteq \xi \sqcap \xi^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma max_inc_xi_cap {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 (max rho xi # ・ max rho xi) ⊆ (xi ∩ xi #).
Proof.
rewrite /max.
rewrite inv_cap_distr.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply cap_inc_compat.
apply inc_residual.
apply cap_r.
apply inv_inc_move.
rewrite comp_inv inv_invol.
apply inc_residual.
apply residual_inc_compat_r.
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[sup\_inc\_xi\_cap]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
(sup(\rho , \xi))^\sharp \cdot sup(\rho , \xi) \sqsubseteq \xi \sqcap \xi^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma sup_inc_xi_cap {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 (sup rho xi # ・ sup rho xi) ⊆ (xi ∩ xi #).
Proof.
move : (@max_inc_xi_cap _ _ (rho △ xi) (xi #)).
rewrite /max/sup.
by [rewrite inv_invol (@cap_comm _ _ xi)].
Qed.

(** %
\begin{screen}
\begin{lemma}[transitive\_sup1]
Let $\rho :V \rel X$, $\xi :X \rel X$ and $\xi \cdot \xi \sqsubseteq \xi$. Then,
$$
sup(\rho , \xi) \cdot (\xi \sqcap \xi^\sharp) = sup(\rho , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma transitive_sup1 {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 (xi ・ xi) ⊆ xi -> sup rho xi ・ (xi ∩ xi #) = sup rho xi.
Proof.
move => H.
apply inc_antisym.
rewrite /sup.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply cap_inc_compat.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
apply (@inc_trans _ _ _ _ _ (residual_property1)).
apply (residual_inc_compat_l H).
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_r)).
apply (@inc_trans _ _ _ _ _ (residual_property1)).
apply residual_inc_compat_l.
rewrite -comp_inv inv_inc_move inv_invol.
apply H.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
rewrite comp_assoc.
apply (comp_inc_compat_ab_ab' sup_inc_xi_cap).
Qed.

(** %
\begin{screen}
\begin{lemma}[transitive\_sup2]
Let $\rho :V \rel X$, $\xi :X \rel X$ and $\xi \cdot \xi \sqsubseteq \xi$. Then,
$$
sup(\rho , \xi) \cdot \xi = \domain{sup(\rho , \xi)} \cdot (\rho \rhd \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma transitive_sup2 {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 (xi ・ xi) ⊆ xi -> sup rho xi ・ xi = domain (sup rho xi) ・ (rho △ xi).
Proof.
move => H.
apply inc_antisym.
replace (sup rho xi ・ xi) with (domain (sup rho xi) ・ (sup rho xi ・ xi)).
apply comp_inc_compat_ab_ab'.
apply (@inc_trans _ _ _ ((rho △ xi) ・ xi)).
apply (comp_inc_compat_ab_a'b cap_l).
apply (@inc_trans _ _ _ _ _ (residual_property1) (residual_inc_compat_l H)).
by [rewrite -comp_assoc domain_comp_alpha1].
apply (@inc_trans _ _ _ (domain (sup rho xi) ・ (sup rho xi △ xi))).
apply comp_inc_compat_ab_ab'.
apply galois.
apply cap_r.
rewrite /domain.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_residual.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_sup\_inc]
Let $\rho :V \rel X$ and $\xi :X \rel X$. Then,
$$
\domain{sup(\rho , \xi)} \cdot \rho \sqsubseteq sup(\rho , \xi) \cdot \xi^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_sup_inc {V X : eqType} {rho : Rel V X} {xi : Rel X X}:
 (domain (sup rho xi) ・ rho) ⊆ (sup rho xi ・ xi #).
Proof.
apply (@inc_trans _ _ _ (domain (sup rho xi) ・ (sup rho xi △ xi #))).
apply comp_inc_compat_ab_ab'.
rewrite -galois.
apply cap_l.
rewrite /domain.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_residual.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[sup\_function]
Let $\rho :V \rel X$, $\xi :X \rel X$ be relations and $f:W \to V$ be a function. Then,
$$
f \cdot sup(\rho , \xi) = sup(f \cdot \rho , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma sup_function {V W X : eqType} {rho : Rel V X} {xi : Rel X X} {f : Rel W V}:
 function_r f -> f ・ sup rho xi = sup (f ・ rho) xi.
Proof.
move => H.
rewrite /sup.
rewrite (function_cap_distr_l H).
by [rewrite (function_residual2 H) (function_residual2 H) (function_residual2 H)].
Qed.

(** %
\begin{screen}
\begin{lemma}[max\_univalent]
Let $\rho :V \rel X$, $\xi :X \rel X$ be relations and $\varphi :W \rel V$ be a univalent relation. Then,
$$
\varphi \cdot max(\rho , \xi) = max(\varphi \cdot \rho , \xi).
$$
\end{lemma}
\end{screen}
% **)
Lemma max_univalent {V W X : eqType}
 {rho : Rel V X} {xi : Rel X X} {phi : Rel W V}:
 univalent_r phi -> phi ・ max rho xi = max (phi ・ rho) xi.
Proof.
move => H.
rewrite /max.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply cap_inc_compat_l.
apply (@inc_trans _ _ _ _ _ (univalent_residual H)).
rewrite double_residual.
apply inc_refl.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
apply cap_inc_compat_l.
rewrite -inc_residual double_residual.
apply inc_refl.
Qed.

(** %
\subsection{左剰余合成}
\begin{screen}
関係 $\alpha :X \rel Y$, $\beta :Y \rel Z$ に対し, 左剰余合成を $\alpha \lhd \beta := (\beta^\sharp \rhd \alpha^\sharp)^\sharp$ で定義する.
\end{screen}
% **)
Definition leftres {X Y Z : eqType} (alpha : Rel X Y) (beta : Rel Y Z)
 := (beta # △ alpha #) #.

(** %
\begin{screen}
\begin{lemma}[inc\_leftres]
Let $\alpha :X \rel Y$, $\beta :Y \rel Z$ and $\delta :X \rel Z$. Then,
$$
\delta \sqsubseteq \alpha \lhd \beta \Leftrightarrow \delta \cdot \beta^\sharp \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_leftres {X Y Z : eqType}
 {alpha : Rel X Y} {beta : Rel Y Z} {delta : Rel X Z}:
 delta ⊆ leftres alpha beta <-> (delta ・ beta #) ⊆ alpha.
Proof.
rewrite /leftres.
by [rewrite inv_inc_move inc_residual -comp_inv inv_inc_move inv_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[residual\_leftres\_assoc]
Let $\alpha :X \rel Y$, $\beta :Y \rel Z$ and $\gamma :Z \rel W$. Then,
$$
(\alpha \rhd \beta) \lhd \gamma = \alpha \rhd (\beta \lhd \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma residual_leftres_assoc {W X Y Z : eqType}
 {alpha : Rel X Y} {beta : Rel Y Z} {gamma : Rel Z W}:
 leftres (alpha △ beta) gamma = alpha △ leftres beta gamma.
Proof.
apply inc_lower.
move => delta.
by [rewrite inc_leftres inc_residual -comp_assoc -inc_leftres -inc_residual].
Qed.

End main.