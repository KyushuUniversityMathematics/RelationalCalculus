Require Import Basic_Notations.
Require Import Logic.Classical_Prop.

(** %
\section{束論に関する補題}
\subsection{和関係, 共通関係}
\begin{screen}
\begin{lemma}[cap\_l]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcap \beta \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_l {A B : eqType} {alpha beta : Rel A B}: (alpha ∩ beta) ⊆ alpha.
Proof.
assert ((alpha ∩ beta) ⊆ (alpha ∩ beta)).
apply inc_refl.
apply inc_cap in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_r]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcap \beta \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_r {A B : eqType} {alpha beta : Rel A B}: (alpha ∩ beta) ⊆ beta.
Proof.
assert ((alpha ∩ beta) ⊆ (alpha ∩ beta)).
apply inc_refl.
apply inc_cap in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_l]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \alpha \sqcup \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_l {A B : eqType} {alpha beta : Rel A B}: alpha ⊆ (alpha ∪ beta).
Proof.
assert ((alpha ∪ beta) ⊆ (alpha ∪ beta)).
apply inc_refl.
apply inc_cup in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_r]
Let $\alpha , \beta :A \rel B$. Then,
$$
\beta \sqsubseteq \alpha \sqcup \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_r {A B : eqType} {alpha beta : Rel A B}: beta ⊆ (alpha ∪ beta).
Proof.
assert ((alpha ∪ beta) ⊆ (alpha ∪ beta)).
apply inc_refl.
apply inc_cup in H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_def1]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha = \alpha \sqcap \beta \Leftrightarrow \alpha \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_def1 {A B : eqType} {alpha beta : Rel A B}:
 alpha = alpha ∩ beta <-> alpha ⊆ beta.
Proof.
split; move => H.
assert (alpha ⊆ (alpha ∩ beta)).
rewrite -H.
apply inc_refl.
apply inc_cap in H0.
apply H0.
apply inc_antisym.
apply inc_cap.
split.
apply inc_refl.
apply H.
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_def2]
Let $\alpha , \beta :A \rel B$. Then,
$$
\beta = \alpha \sqcup \beta \Leftrightarrow \alpha \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_def2 {A B : eqType} {alpha beta : Rel A B}:
 beta = alpha ∪ beta <-> alpha ⊆ beta.
Proof.
split; move => H.
assert ((alpha ∪ beta) ⊆ beta).
rewrite -H.
apply inc_refl.
apply inc_cup in H0.
apply H0.
apply inc_antisym.
assert ((alpha ∪ beta) ⊆ (alpha ∪ beta)).
apply inc_refl.
apply cup_r.
apply inc_cup.
split.
apply H.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_assoc]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \sqcap \beta) \sqcap \gamma = \alpha \sqcap (\beta \sqcap \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_assoc {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha ∩ beta) ∩ gamma = alpha ∩ (beta ∩ gamma).
Proof.
apply inc_antisym.
rewrite inc_cap.
split.
apply (inc_trans _ _ _ (alpha ∩ beta)).
apply cap_l.
apply cap_l.
rewrite inc_cap.
split.
apply (inc_trans _ _ _ (alpha ∩ beta)).
apply cap_l.
apply cap_r.
apply cap_r.
rewrite inc_cap.
split.
rewrite inc_cap.
split.
apply cap_l.
apply (inc_trans _ _ _ (beta ∩ gamma)).
apply cap_r.
apply cap_l.
apply (inc_trans _ _ _ (beta ∩ gamma)).
apply cap_r.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_assoc]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \sqcup \beta) \sqcup \gamma = \alpha \sqcup (\beta \sqcup \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_assoc {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha ∪ beta) ∪ gamma = alpha ∪ (beta ∪ gamma).
Proof.
apply inc_antisym.
rewrite inc_cup.
split.
rewrite inc_cup.
split.
apply cup_l.
apply (inc_trans _ _ _ (beta ∪ gamma)).
apply cup_l.
apply cup_r.
apply (inc_trans _ _ _ (beta ∪ gamma)).
apply cup_r.
apply cup_r.
rewrite inc_cup.
split.
apply (inc_trans _ _ _ (alpha ∪ beta)).
apply cup_l.
apply cup_l.
rewrite inc_cup.
split.
apply (inc_trans _ _ _ (alpha ∪ beta)).
apply cup_r.
apply cup_l.
apply cup_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_comm]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcap \beta = \beta \sqcap \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_comm {A B : eqType} {alpha beta : Rel A B}: alpha ∩ beta = beta ∩ alpha.
Proof.
apply inc_antisym.
rewrite inc_cap.
split.
apply cap_r.
apply cap_l.
rewrite inc_cap.
split.
apply cap_r.
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_comm]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcup \beta = \beta \sqcup \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_comm {A B : eqType} {alpha beta : Rel A B}: alpha ∪ beta = beta ∪ alpha.
Proof.
apply inc_antisym.
rewrite inc_cup.
split.
apply cup_r.
apply cup_l.
rewrite inc_cup.
split.
apply cup_r.
apply cup_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_cap\_abs]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcup (\alpha \sqcap \beta) = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_cap_abs {A B : eqType} {alpha beta : Rel A B}:
 alpha ∪ (alpha ∩ beta) = alpha.
Proof.
move : (@cap_l _ _ alpha beta) => H.
apply inc_def2 in H.
by [rewrite cup_comm -H].
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cup\_abs]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcap (\alpha \sqcup \beta) = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cup_abs {A B : eqType} {alpha beta : Rel A B}:
 alpha ∩ (alpha ∪ beta) = alpha.
Proof.
move : (@cup_l _ _ alpha beta) => H.
apply inc_def1 in H.
by [rewrite  -H].
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_idem]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcap \alpha = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_idem {A B : eqType} {alpha : Rel A B}: alpha ∩ alpha = alpha.
Proof.
apply inc_antisym.
apply cap_l.
apply inc_cap.
split; apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_idem]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcup \alpha = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_idem {A B : eqType} {alpha : Rel A B}: alpha ∪ alpha = alpha.
Proof.
apply inc_antisym.
apply inc_cup.
split; apply inc_refl.
apply cup_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_inc\_compat]
Let $\alpha , {\alpha}' , \beta , {\beta}' :A \rel B$. Then,
$$
\alpha \sqsubseteq {\alpha}' \land \beta \sqsubseteq {\beta}' \Rightarrow \alpha \sqcap \beta \sqsubseteq {\alpha}' \sqcap {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_inc_compat {A B : eqType} {alpha alpha' beta beta' : Rel A B}:
 alpha ⊆ alpha' -> beta ⊆ beta' -> (alpha ∩ beta) ⊆ (alpha' ∩ beta').
Proof.
move => H H0.
rewrite -inc_def1.
apply inc_def1 in H.
apply inc_def1 in H0.
rewrite cap_assoc -(@cap_assoc _ _ beta).
rewrite (@cap_comm _ _ beta).
rewrite cap_assoc -(@cap_assoc _ _ alpha).
by [rewrite -H -H0].
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_inc\_compat\_l]
Let $\alpha , \beta , {\beta}' :A \rel B$. Then,
$$
\beta \sqsubseteq {\beta}' \Rightarrow \alpha \sqcap \beta \sqsubseteq \alpha \sqcap {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_inc_compat_l {A B : eqType} {alpha beta beta' : Rel A B}:
 beta ⊆ beta' -> (alpha ∩ beta) ⊆ (alpha ∩ beta').
Proof.
move => H.
apply (@cap_inc_compat _ _ _ _ _ _ (@inc_refl _ _ alpha) H).
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_inc\_compat\_r]
Let $\alpha , {\alpha}' , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq {\alpha}' \Rightarrow \alpha \sqcap \beta \sqsubseteq {\alpha}' \sqcap \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_inc_compat_r {A B : eqType} {alpha alpha' beta : Rel A B}:
 alpha ⊆ alpha' -> (alpha ∩ beta) ⊆ (alpha' ∩ beta).
Proof.
move => H.
apply (@cap_inc_compat _ _ _ _ _ _ H (@inc_refl _ _ beta)).
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_inc\_compat]
Let $\alpha , {\alpha}' , \beta , {\beta}' :A \rel B$. Then,
$$
\alpha \sqsubseteq {\alpha}' \land \beta \sqsubseteq {\beta}' \Rightarrow \alpha \sqcup \beta \sqsubseteq {\alpha}' \sqcup {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_inc_compat {A B : eqType} {alpha alpha' beta beta' : Rel A B}:
 alpha ⊆ alpha' -> beta ⊆ beta' -> (alpha ∪ beta) ⊆ (alpha' ∪ beta').
Proof.
move => H H0.
rewrite -inc_def2.
apply inc_def2 in H.
apply inc_def2 in H0.
rewrite cup_assoc -(@cup_assoc _ _ beta).
rewrite (@cup_comm _ _ beta).
rewrite cup_assoc -(@cup_assoc _ _ alpha).
by [rewrite -H -H0].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_inc\_compat\_l]
Let $\alpha , \beta , {\beta}' :A \rel B$. Then,
$$
\beta \sqsubseteq {\beta}' \Rightarrow \alpha \sqcup \beta \sqsubseteq \alpha \sqcup {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_inc_compat_l {A B : eqType} {alpha beta beta' : Rel A B}:
 beta ⊆ beta' -> (alpha ∪ beta) ⊆ (alpha ∪ beta').
Proof.
move => H.
apply (@cup_inc_compat _ _ _ _ _ _ (@inc_refl _ _ alpha) H).
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_inc\_compat\_r]
Let $\alpha , {\alpha}' , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq {\alpha}' \Rightarrow \alpha \sqcup \beta \sqsubseteq {\alpha}' \sqcup \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_inc_compat_r {A B : eqType} {alpha alpha' beta : Rel A B}:
 alpha ⊆ alpha' -> (alpha ∪ beta) ⊆ (alpha' ∪ beta).
Proof.
move => H.
apply (@cup_inc_compat _ _ _ _ _ _ H (@inc_refl _ _ beta)).
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_empty]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcap \phi_{AB} = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_empty {A B : eqType} {alpha : Rel A B}: alpha ∩ φ A B = φ A B.
Proof.
apply inc_antisym.
apply cap_r.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_empty]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcup \phi_{AB} = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_empty {A B : eqType} {alpha : Rel A B}: alpha ∪ φ A B = alpha.
Proof.
apply inc_antisym.
apply inc_cup.
split.
apply inc_refl.
apply inc_empty_alpha.
apply cup_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_universal]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcap \nabla_{AB} = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_universal {A B : eqType} {alpha : Rel A B}: alpha ∩ ∇ A B = alpha.
Proof.
apply inc_antisym.
apply cap_l.
apply inc_cap.
split.
apply inc_refl.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_universal]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcup \nabla_{AB} = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_universal {A B : eqType} {alpha : Rel A B}: alpha ∪ ∇ A B = ∇ A B.
Proof.
apply inc_antisym.
apply inc_cup.
split.
apply inc_alpha_universal.
apply inc_refl.
apply cup_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_lower]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha = \beta \Leftrightarrow (\forall \gamma :A \rel B, \gamma \sqsubseteq \alpha \Leftrightarrow \gamma \sqsubseteq \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_lower {A B : eqType} {alpha beta : Rel A B}:
 alpha = beta <-> (forall gamma : Rel A B, gamma ⊆ alpha <-> gamma ⊆ beta).
Proof.
split; move => H.
move => gamma.
by [rewrite H].
apply inc_antisym.
rewrite -H.
apply inc_refl.
rewrite H.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_upper]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha = \beta \Leftrightarrow (\forall \gamma :A \rel B, \alpha \sqsubseteq \gamma \Leftrightarrow \beta \sqsubseteq \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_upper {A B : eqType} {alpha beta : Rel A B}:
 alpha = beta <-> (forall gamma : Rel A B, alpha ⊆ gamma <-> beta ⊆ gamma).
Proof.
split; move => H.
move => gamma.
by [rewrite H].
apply inc_antisym.
rewrite H.
apply inc_refl.
rewrite -H.
apply inc_refl.
Qed.

(** %
\subsection{分配法則}
\begin{screen}
\begin{lemma}[cap\_cup\_distr\_l]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqcap (\beta \sqcup \gamma) = (\alpha \sqcap \beta) \sqcup (\alpha \sqcap \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cup_distr_l {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha ∩ (beta ∪ gamma) = (alpha ∩ beta) ∪ (alpha ∩ gamma).
Proof.
apply inc_upper.
move => delta.
split; move => H.
rewrite cap_comm (@cap_comm _ _ _ gamma).
apply inc_cup.
rewrite -inc_rpc -inc_rpc.
apply inc_cup.
rewrite inc_rpc cap_comm.
apply H.
rewrite cap_comm -inc_rpc.
apply inc_cup.
rewrite inc_rpc inc_rpc.
apply inc_cup.
rewrite cap_comm (@cap_comm _ _ gamma).
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cup\_distr\_r]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \sqcup \beta) \sqcap \gamma = (\alpha \sqcap \gamma) \sqcup (\beta \sqcap \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cup_distr_r {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha ∪ beta) ∩ gamma = (alpha ∩ gamma) ∪ (beta ∩ gamma).
Proof.
rewrite (@cap_comm _ _ (alpha ∪ beta)) (@cap_comm _ _ alpha) (@cap_comm _ _ beta).
apply cap_cup_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_cap\_distr\_l]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqcup (\beta \sqcap \gamma) = (\alpha \sqcup \beta) \sqcap (\alpha \sqcup \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_cap_distr_l {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha ∪ (beta ∩ gamma) = (alpha ∪ beta) ∩ (alpha ∪ gamma).
Proof.
rewrite cap_cup_distr_l.
rewrite (@cap_comm _ _ (alpha ∪ beta)) cap_cup_abs (@cap_comm _ _ (alpha ∪ beta)).
rewrite cap_cup_distr_l.
rewrite -cup_assoc (@cap_comm _ _ gamma) cup_cap_abs.
by [rewrite cap_comm].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_cap\_distr\_r]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \sqcap \beta) \sqcup \gamma = (\alpha \sqcup \gamma) \sqcap (\beta \sqcup \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_cap_distr_r {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha ∩ beta) ∪ gamma = (alpha ∪ gamma) ∩ (beta ∪ gamma).
Proof.
rewrite (@cup_comm _ _ (alpha ∩ beta)) (@cup_comm _ _ alpha) (@cup_comm _ _ beta).
apply cup_cap_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cup\_unique]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqcap \beta = \alpha \sqcap \gamma \land \alpha \sqcup \beta = \alpha \sqcup \gamma \Rightarrow \beta = \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cup_unique {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha ∩ beta = alpha ∩ gamma -> alpha ∪ beta = alpha ∪ gamma -> beta = gamma.
Proof.
move => H H0.
rewrite -(@cap_cup_abs _ _ beta alpha) cup_comm H0.
rewrite cap_cup_distr_l.
rewrite cap_comm H.
rewrite -cap_cup_distr_r.
rewrite H0 cap_comm cup_comm.
apply cap_cup_abs.
Qed.

(** %
\subsection{原子性}
\begin{screen}
空関係でない $\alpha :A \rel B$ が, 任意の $\beta :A \rel B$ について
$$
\beta \sqsubseteq \alpha \Rightarrow \beta = \phi_{AB} \lor \beta = \alpha
$$
を満たすとき, $\alpha$ は原子的 (atomic) であると言われる.
\end{screen}
% **)
Definition atomic {A B : eqType} (alpha : Rel A B):=
 alpha <> φ A B /\ (forall beta : Rel A B, beta ⊆ alpha -> beta = φ A B \/ beta = alpha).

(** %
\begin{screen}
\begin{lemma}[atomic\_cap\_empty]
Let $\alpha, \beta :A \rel B$ are atomic and $\alpha \neq \beta$. Then,
$$
\alpha \sqcap \beta = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma atomic_cap_empty {A B : eqType} {alpha beta : Rel A B}:
 atomic alpha -> atomic beta -> alpha <> beta -> alpha ∩ beta = φ A B.
Proof.
move => H H0.
apply or_to_imply.
case (classic (alpha ∩ beta = φ A B)); move => H1.
right.
apply H1.
left.
move => H2.
apply H2.
apply inc_antisym.
apply inc_def1.
elim H => H3 H4.
case (H4 (alpha ∩ beta) (cap_l)); move => H5.
apply False_ind.
apply (H1 H5).
by [rewrite H5].
apply inc_def1.
elim H0 => H3 H4.
case (H4 (alpha ∩ beta) (cap_r)); move => H5.
apply False_ind.
apply (H1 H5).
by [rewrite cap_comm H5].
Qed.

(** %
\begin{screen}
\begin{lemma}[atomic\_cup]
Let $\alpha, \beta, \gamma :A \rel B$ and $\alpha$ is atomic. Then,
$$
\alpha \sqsubseteq \beta \sqcup \gamma \Rightarrow \alpha \sqsubseteq \beta \lor \alpha \sqsubseteq \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma atomic_cup {A B : eqType} {alpha beta gamma : Rel A B}:
 atomic alpha -> alpha ⊆ (beta ∪ gamma) -> alpha ⊆ beta \/ alpha ⊆ gamma.
Proof.
move => H H0.
apply inc_def1 in H0.
rewrite cap_cup_distr_l in H0.
elim H => H1 H2.
rewrite H0 in H1.
assert (alpha ∩ beta <> φ A B \/ alpha ∩ gamma <> φ A B).
apply not_and_or.
elim => H3 H4.
rewrite H3 H4 in H1.
apply H1.
by [rewrite cup_empty].
case H3; move => H4.
left.
apply inc_def1.
case (H2 (alpha ∩ beta) (cap_l)); move => H5.
apply False_ind.
apply (H4 H5).
by [rewrite H5].
right.
apply inc_def1.
case (H2 (alpha ∩ gamma) (cap_l)); move => H5.
apply False_ind.
apply (H4 H5).
by [rewrite H5].
Qed.

(** %
\section{Heyting 代数に関する補題}
\begin{screen}
\begin{lemma}[rpc\_universal]
Let $\alpha :A \rel B$. Then,
$$
(\alpha \Rightarrow \alpha) = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_universal {A B : eqType} {alpha : Rel A B}: (alpha >> alpha) = ∇ A B.
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_alpha_universal.
apply inc_rpc.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_r]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) \sqcap \beta = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_r {A B : eqType} {alpha beta : Rel A B}: (alpha >> beta) ∩ beta = beta.
Proof.
assert (beta ⊆ (alpha >> beta)).
apply inc_rpc.
apply cap_l.
apply inc_def1 in H.
by [rewrite cap_comm -H].
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_def3]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) = \nabla_{AB} \Leftrightarrow \alpha \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inc_def3 {A B : eqType} {alpha beta : Rel A B}:
 (alpha >> beta) = ∇ A B <-> alpha ⊆ beta.
Proof.
split; move => H.
rewrite -(@rpc_universal _ _ alpha) in H.
assert ((alpha >> alpha) ⊆ (alpha >> beta)).
rewrite H.
apply inc_refl.
apply inc_rpc in H0.
rewrite rpc_r in H0.
apply H0.
apply inc_antisym.
apply inc_alpha_universal.
rewrite -(@rpc_universal _ _ alpha).
apply inc_rpc.
rewrite rpc_r.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_l]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqcap (\alpha \Rightarrow \beta) = \alpha \sqcap \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_l {A B : eqType} {alpha beta : Rel A B}:
 alpha ∩ (alpha >> beta) = alpha ∩ beta.
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_cap.
apply inc_cap in H.
split.
apply H.
elim H => H0 H1.
apply inc_rpc in H1.
rewrite -(@cap_idem _ _ gamma).
apply (inc_trans _ _ _ (gamma ∩ alpha)).
apply cap_inc_compat.
apply inc_refl.
apply H0.
apply H1.
apply inc_cap.
apply inc_cap in H.
split.
apply H.
apply inc_rpc.
apply (inc_trans _ _ _ gamma).
apply cap_l.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_inc\_compat]
Let $\alpha , {\alpha}' , \beta , {\beta}' :A \rel B$. Then,
$$
{\alpha}' \sqsubseteq \alpha \land \beta \sqsubseteq {\beta}' \Rightarrow (\alpha \Rightarrow \beta) \sqsubseteq ({\alpha}' \Rightarrow {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_inc_compat {A B : eqType} {alpha alpha' beta beta' : Rel A B}:
 alpha' ⊆ alpha -> beta ⊆ beta' -> (alpha >> beta) ⊆ (alpha' >> beta').
Proof.
move => H H0.
apply inc_rpc.
apply (@inc_trans _ _ _ ((alpha >> beta) ∩ alpha)).
apply (@cap_inc_compat_l _ _ _ _ _ H).
rewrite cap_comm rpc_l.
apply (@inc_trans _ _ _ beta).
apply cap_r.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_inc\_compat\_l]
Let $\alpha , \beta , {\beta}' :A \rel B$. Then,
$$
\beta \sqsubseteq {\beta}' \Rightarrow (\alpha \Rightarrow \beta) \sqsubseteq (\alpha \Rightarrow {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_inc_compat_l {A B : eqType} {alpha beta beta' : Rel A B}:
 beta ⊆ beta' -> (alpha >> beta) ⊆ (alpha >> beta').
Proof.
move => H.
apply (@rpc_inc_compat _ _ _ _ _ _ (@inc_refl _ _ alpha) H).
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_inc\_compat\_r]
Let $\alpha , {\alpha}' , \beta :A \rel B$. Then,
$$
{\alpha}' \sqsubseteq \alpha \Rightarrow (\alpha \Rightarrow \beta) \sqsubseteq ({\alpha}' \Rightarrow \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_inc_compat_r {A B : eqType} {alpha alpha' beta : Rel A B}:
 alpha' ⊆ alpha -> (alpha >> beta) ⊆ (alpha' >> beta).
Proof.
move => H.
apply (@rpc_inc_compat _ _ _ _ _ _ H (@inc_refl _ _ beta)).
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_universal\_alpha]
Let $\alpha :A \rel B$. Then,
$$
\nabla_{AB} \Rightarrow \alpha = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_universal_alpha {A B : eqType} {alpha : Rel A B}: ∇ A B >> alpha = alpha.
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_rpc in H.
rewrite cap_universal in H.
apply H.
apply inc_rpc.
rewrite cap_universal.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma1]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) \sqsubseteq ((\alpha \sqcap \gamma) \Rightarrow (\beta \sqcap \gamma)).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma1 {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha >> beta) ⊆ ((alpha ∩ gamma) >> (beta ∩ gamma)).
Proof.
apply inc_rpc.
rewrite -cap_assoc (@cap_comm _ _ _ alpha).
rewrite rpc_l.
apply cap_inc_compat_r.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma2]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) \sqcap (\alpha \Rightarrow \gamma) = (\alpha \Rightarrow (\beta \sqcap \gamma)).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma2 {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha >> beta) ∩ (alpha >> gamma) = alpha >> (beta ∩ gamma).
Proof.
apply inc_lower.
move => delta.
split; move => H.
rewrite inc_rpc.
apply inc_cap in H.
apply inc_cap.
rewrite -inc_rpc -inc_rpc.
apply H.
apply inc_cap.
rewrite inc_rpc inc_rpc.
apply inc_cap.
rewrite -inc_rpc.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma3]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) \sqcap (\beta \Rightarrow \gamma) \sqsubseteq ((\alpha \sqcup \beta) \Rightarrow (\beta \sqcap \gamma)).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma3 {A B : eqType} {alpha beta gamma : Rel A B}:
 ((alpha >> beta) ∩ (beta >> gamma)) ⊆ ((alpha ∪ beta) >> (beta ∩ gamma)).
Proof.
apply inc_rpc.
rewrite cap_cup_distr_l.
rewrite cap_comm -cap_assoc rpc_l.
rewrite (@cap_assoc _ _ _ _ beta) (@cap_comm _ _ (beta >> gamma)) -cap_assoc rpc_r.
rewrite cap_assoc rpc_l.
apply inc_cup.
split.
apply cap_r.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma4]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) \sqcap (\beta \Rightarrow \gamma) \sqsubseteq (\alpha \Rightarrow \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma4 {A B : eqType} {alpha beta gamma : Rel A B}:
 ((alpha >> beta) ∩ (beta >> gamma)) ⊆ (alpha >> gamma).
Proof.
apply (@inc_trans _ _ _ ((alpha ∪ beta) >> (beta ∩ gamma))).
apply rpc_lemma3.
apply rpc_inc_compat.
apply cup_l.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma5]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \Rightarrow (\beta \Rightarrow \gamma) = (\alpha \sqcap \beta) \Rightarrow \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma5 {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha >> (beta >> gamma) = (alpha ∩ beta) >> gamma.
Proof.
apply inc_lower.
move => delta.
split; move => H.
apply inc_rpc.
rewrite -cap_assoc.
rewrite -inc_rpc -inc_rpc.
apply H.
rewrite inc_rpc inc_rpc.
rewrite cap_assoc.
apply inc_rpc.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma6]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \Rightarrow (\beta \Rightarrow \gamma) \sqsubseteq (\alpha \Rightarrow \beta) \Rightarrow (\alpha \Rightarrow \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma6 {A B : eqType} {alpha beta gamma : Rel A B}:
 (alpha >> (beta >> gamma)) ⊆ ((alpha >> beta) >> (alpha >> gamma)).
Proof.
rewrite inc_rpc inc_rpc.
rewrite cap_assoc (@cap_comm _ _ _ alpha).
rewrite rpc_l.
rewrite -cap_assoc (@cap_comm _ _ _ alpha).
rewrite rpc_l.
rewrite cap_assoc (@cap_comm _ _ _ beta).
rewrite rpc_l.
rewrite -cap_assoc.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_lemma7]
Let $\alpha , \beta , \gamma , \delta :A \rel B$ and $\beta \sqsubseteq \alpha \sqsubseteq \gamma$. Then,
$$
(\alpha \sqcap \delta = \beta) \land (\alpha \sqcup \delta = \gamma) \Leftrightarrow (\gamma \sqsubseteq \alpha \sqcup (\alpha \Rightarrow \beta)) \land (\delta = \gamma \sqcap (\alpha \Rightarrow \beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_lemma7 {A B : eqType} {alpha beta gamma delta : Rel A B}:
beta ⊆ alpha -> alpha ⊆ gamma -> (alpha ∩ delta = beta /\ alpha ∪ delta = gamma
 <-> gamma ⊆ (alpha ∪ (alpha >> beta)) /\ delta = gamma ∩ (alpha >> beta)).
Proof.
move => H H0.
split; elim; move => H1 H2; split.
rewrite -H2.
apply cup_inc_compat_l.
apply inc_rpc.
rewrite cap_comm H1.
apply inc_refl.
rewrite -H2.
rewrite cap_cup_distr_r rpc_l.
assert (delta ⊆ (alpha >> beta)).
apply inc_rpc.
rewrite cap_comm H1.
apply inc_refl.
apply inc_def1 in H3.
rewrite -H3 -H1.
rewrite -cap_assoc cap_idem.
by [rewrite cap_comm cup_comm cup_cap_abs].
rewrite H2.
rewrite (@cap_comm _ _ gamma) -cap_assoc rpc_l.
apply inc_antisym.
apply (@inc_trans _ _ _ (beta ∩ gamma)).
apply cap_inc_compat_r.
apply cap_r.
apply cap_l.
move : (@inc_trans _ _ _ _ _ H H0) => H3.
apply inc_def1 in H.
apply inc_def1 in H3.
rewrite cap_comm in H.
rewrite -H -H3.
apply inc_refl.
rewrite H2.
rewrite cup_cap_distr_l.
apply inc_def2 in H0.
rewrite -H0.
apply inc_def1 in H1.
by [rewrite -H1].
Qed.

(** %
\section{補関係に関する補題}
\begin{screen}
\begin{lemma}[complement\_universal]
$$
{\nabla_{AB}}^- = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma complement_universal {A B : eqType}: ∇ A B ^ = φ A B.
Proof.
apply rpc_universal_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[complement\_alpha\_universal]
Let $\alpha :A \rel B$. Then,
$$
\alpha^- = \nabla_{AB} \Leftrightarrow \alpha = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma complement_alpha_universal {A B : eqType} {alpha : Rel A B}:
 alpha ^ = ∇ A B <-> alpha = φ A B.
Proof.
split; move => H.
apply inc_antisym.
rewrite -(@cap_universal _ _ alpha) cap_comm.
apply inc_rpc.
rewrite -H.
apply inc_refl.
apply inc_empty_alpha.
apply inc_antisym.
apply inc_alpha_universal.
apply inc_rpc.
rewrite cap_comm cap_universal.
rewrite H.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[complement\_empty]
$$
{\phi_{AB}}^- = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma complement_empty {A B : eqType}: φ A B ^ = ∇ A B.
Proof.
by [apply complement_alpha_universal].
Qed.

(** %
\begin{screen}
\begin{lemma}[complement\_invol\_inc]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqsubseteq (\alpha^-)^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma complement_invol_inc {A B : eqType} {alpha : Rel A B}: alpha ⊆ (alpha ^) ^.
Proof.
apply inc_rpc.
rewrite cap_comm.
apply inc_rpc.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_complement\_empty]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcap \alpha^- = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_complement_empty {A B : eqType} {alpha : Rel A B}:
 alpha ∩ alpha ^ = φ A B.
Proof.
apply inc_antisym.
rewrite cap_comm.
apply inc_rpc.
apply inc_refl.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[complement\_invol]
Let $\alpha :A \rel B$. Then,
$$
(\alpha^-)^- = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma complement_invol {A B : eqType} {alpha : Rel A B}: (alpha ^) ^ = alpha.
Proof.
rewrite -(@cap_universal _ _ ((alpha ^) ^)).
rewrite -(@complement_classic _ _ alpha).
rewrite cap_cup_distr_l.
rewrite (@cap_comm _ _ _ (alpha ^)) cap_complement_empty.
rewrite cup_empty cap_comm.
apply Logic.eq_sym.
apply inc_def1.
apply complement_invol_inc.
Qed.

(** %
\begin{screen}
\begin{lemma}[complement\_move]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha = \beta^- \Leftrightarrow \alpha^- = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma complement_move {A B : eqType} {alpha beta : Rel A B}:
 alpha = beta ^ <-> alpha ^ = beta.
Proof.
split; move => H.
by [rewrite H complement_invol].
by [rewrite -H complement_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[contraposition]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) = (\beta^- \Rightarrow \alpha^-).
$$
\end{lemma}
\end{screen}
% **)
Lemma contraposition {A B : eqType} {alpha beta : Rel A B}:
 alpha >> beta = beta ^ >> alpha ^.
Proof.
apply inc_antisym.
apply inc_rpc.
apply rpc_lemma4.
replace (alpha >> beta) with ((alpha ^) ^ >> (beta ^) ^).
apply inc_rpc.
apply rpc_lemma4.
by [rewrite complement_invol complement_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[de\_morgan1]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha \sqcup \beta)^- = \alpha^- \sqcap \beta^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma de_morgan1 {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∪ beta) ^ = alpha ^ ∩ beta ^.
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_cap.
rewrite inc_rpc inc_rpc.
apply inc_cup.
rewrite -cap_cup_distr_l.
apply inc_rpc.
apply H.
apply inc_rpc.
rewrite cap_cup_distr_l.
apply inc_cup.
rewrite -inc_rpc -inc_rpc.
apply inc_cap.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[de\_morgan2]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha \sqcap \beta)^- = \alpha^- \sqcup \beta^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma de_morgan2 {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∩ beta) ^ = alpha ^ ∪ beta ^.
Proof.
by [rewrite -complement_move de_morgan1 complement_invol complement_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_to\_rpc]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha^- \sqcup \beta = (\alpha \Rightarrow \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_to_rpc {A B : eqType} {alpha beta : Rel A B}:
 alpha ^ ∪ beta = alpha >> beta.
Proof.
apply inc_antisym.
apply inc_rpc.
rewrite cap_cup_distr_r cap_comm.
rewrite cap_complement_empty cup_comm cup_empty.
apply cap_l.
rewrite -(@cap_universal _ _ (alpha >> beta)) cap_comm.
rewrite -(@complement_classic _ _ alpha).
rewrite cap_cup_distr_r cup_comm.
apply cup_inc_compat.
apply cap_l.
rewrite rpc_l.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[beta\_contradiction]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta) \sqcap (\alpha \Rightarrow \beta^-) = \alpha^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma beta_contradiction {A B : eqType} {alpha beta : Rel A B}:
 (alpha >> beta) ∩ (alpha >> beta ^) = alpha^.
Proof.
rewrite -cup_to_rpc -cup_to_rpc.
rewrite -cup_cap_distr_l.
by [rewrite cap_complement_empty cup_empty].
Qed.

(** %
\section{Bool 代数に関する補題}
\begin{screen}
\begin{lemma}[bool\_lemma1]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \Leftrightarrow \nabla_{AB} = \alpha^- \sqcup \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma bool_lemma1 {A B : eqType} {alpha beta : Rel A B}:
 alpha ⊆ beta <-> ∇ A B = alpha ^ ∪ beta.
Proof.
split; move => H.
apply inc_antisym.
rewrite -(@complement_classic _ _ alpha) cup_comm.
apply cup_inc_compat_l.
apply H.
apply inc_alpha_universal.
apply inc_def3.
rewrite H.
apply (Logic.eq_sym cup_to_rpc).
Qed.

(** %
\begin{screen}
\begin{lemma}[bool\_lemma2]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \Leftrightarrow \alpha \sqcap \beta^- = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma bool_lemma2 {A B : eqType} {alpha beta : Rel A B}:
 alpha ⊆ beta <-> alpha ∩ beta ^ = φ A B.
Proof.
split; move => H.
rewrite -(@cap_universal _ _ (alpha ∩ beta ^)).
apply bool_lemma1 in H.
rewrite H.
rewrite cap_cup_distr_l.
rewrite (@cap_comm _ _ alpha) cap_assoc cap_complement_empty cap_empty.
rewrite cap_comm -cap_assoc cap_complement_empty cap_comm cap_empty.
by [rewrite cup_empty].
rewrite -(@cap_universal _ _ alpha).
rewrite -(@complement_classic _ _ beta).
rewrite cap_cup_distr_l.
rewrite H cup_empty.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[bool\_lemma3]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \sqcup \gamma \Leftrightarrow \alpha \sqcap \beta^- \sqsubseteq \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma bool_lemma3 {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha ⊆ (beta ∪ gamma) <-> (alpha ∩ beta ^) ⊆ gamma.
Proof.
split; move => H.
apply (@inc_trans _ _ _ ((beta ∪ gamma) ∩ beta ^)).
apply cap_inc_compat_r.
apply H.
rewrite cap_cup_distr_r.
rewrite cap_complement_empty cup_comm cup_empty.
apply cap_l.
apply (@inc_trans _ _ _ (beta ∪ (alpha ∩ beta ^))).
rewrite cup_cap_distr_l.
rewrite complement_classic cap_universal.
apply cup_r.
apply cup_inc_compat_l.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[bool\_lemma4]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \sqcup \gamma \Leftrightarrow \beta^- \sqsubseteq \alpha^- \sqcup \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma bool_lemma4 {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha ⊆ (beta ∪ gamma) <-> beta ^ ⊆ (alpha ^ ∪ gamma).
Proof.
rewrite bool_lemma3.
rewrite cap_comm.
apply iff_sym.
replace (beta ^ ∩ alpha) with (beta ^ ∩ (alpha ^) ^).
apply bool_lemma3.
by [rewrite complement_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[bool\_lemma5]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \sqcup \gamma \Leftrightarrow \nabla_{AB} = \alpha^- \sqcup \beta \sqcup \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma bool_lemma5 {A B : eqType} {alpha beta gamma : Rel A B}:
 alpha ⊆ (beta ∪ gamma) <-> ∇ A B = (alpha ^ ∪ beta) ∪ gamma.
Proof.
rewrite bool_lemma1.
by [rewrite cup_assoc].
Qed.