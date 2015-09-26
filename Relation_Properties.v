Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.Classical_Prop.

(** %
\section{関係計算の基本的な性質}
% **)

(** %
\begin{screen}
\begin{lemma}[RelAB\_unique]
$$
\phi_{AB} = \nabla_{AB} \Leftrightarrow \forall \alpha , \beta :A \rel B, \alpha = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma RelAB_unique {A B : eqType}:
φ A B = ∇ A B <-> (forall alpha beta : Rel A B, alpha = beta).
Proof.
split; move => H.
move => alpha beta.
replace beta with (φ A B).
apply inc_antisym.
rewrite H.
apply inc_alpha_universal.
apply inc_empty_alpha.
apply inc_antisym.
apply inc_empty_alpha.
rewrite H.
apply inc_alpha_universal.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[either\_empty]
$$
\phi_{AB} = \nabla_{AB} \Leftrightarrow A = \emptyset \lor B = \emptyset.
$$
\end{lemma}
\end{screen}
% **)
Lemma either_empty {A B : eqType}: φ A B = ∇ A B <-> (A -> False) \/ (B -> False).
Proof.
rewrite RelAB_unique.
split; move => H.
case (classic (exists _ : A, True)).
elim => a H0.
right.
move => b.
remember (fun (_ : A) (_ : B) => True) as T.
remember (fun (_ : A) (_ : B) => False) as F.
move : (H T F) => H1.
assert (T a b = F a b).
by [rewrite H1].
rewrite HeqT HeqF in H2.
rewrite -H2.
apply I.
move => H0.
left.
move => a.
apply H0.
exists a.
apply I.
move => alpha beta.
assert (A -> B -> False).
move => a b.
case H; move => H0.
apply (H0 a).
apply (H0 b).
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply False_ind.
apply (H0 a b).
Qed.

(** %
\begin{screen}
\begin{lemma}[unit\_empty\_not\_universal]
$$
\phi_{II} \neq \nabla_{II}.
$$
\end{lemma}
\end{screen}
% **)
Lemma unit_empty_not_universal : φ i i <> ∇ i i.
Proof.
move => H.
apply either_empty in H.
case H; move => H0.
apply (H0 tt).
apply (H0 tt).
Qed.

(** %
\begin{screen}
\begin{lemma}[unit\_empty\_or\_universal]
Let $\alpha :I \rel I$. Then,
$$
\alpha = \phi_{II} \lor \alpha = \nabla_{II}.
$$
\end{lemma}
\end{screen}
% **)
Lemma unit_empty_or_universal {alpha : Rel i i}: alpha = φ i i \/ alpha = ∇ i i.
Proof.
assert (forall beta : Rel i i, beta = (fun (_ _ : i) => True) \/ beta = (fun (_ _ : i) => False)).
move => beta.
case (classic (beta tt tt)); move => H.
left.
apply functional_extensionality.
induction x.
apply functional_extensionality.
induction x.
apply prop_extensionality_ok.
split; move => H0.
apply I.
apply H.
right.
apply functional_extensionality.
induction x.
apply functional_extensionality.
induction x.
apply prop_extensionality_ok.
split.
apply H.
apply False_ind.
assert ((fun _ _ : i => True) <> (fun _ _ : i => False)).
move => H0.
remember (fun _ _ : i => True) as T.
remember (fun _ _ : i => False) as F.
assert (T tt tt = F tt tt).
by [rewrite H0].
rewrite HeqT HeqF in H1.
rewrite -H1.
apply I.
case (H (φ i i)); move => H1.
case (H (∇ i i)); move => H2.
apply False_ind.
apply unit_empty_not_universal.
by [rewrite H1 H2].
case (H alpha); move => H3.
left.
by [rewrite H3 H1].
right.
by [rewrite H3 H2].
case (H (∇ i i)); move => H2.
case (H alpha); move => H3.
right.
by [rewrite H3 H2].
left.
by [rewrite H3 H1].
apply False_ind.
apply unit_empty_not_universal.
by [rewrite H1 H2].
Qed.

(** %
\begin{screen}
\begin{lemma}[unit\_identity\_is\_universal]
$$
id_I = \nabla_{II}.
$$
\end{lemma}
\end{screen}
% **)
Lemma unit_identity_is_universal : Id i = ∇ i i.
Proof.
case (@unit_empty_or_universal (Id i)); move => H.
apply False_ind.
assert (Id i ⊆ (∇ i i # △ φ i i)).
rewrite H.
apply inc_empty_alpha.
apply inc_residual in H0.
rewrite inv_invol comp_id_r in H0.
apply unit_empty_not_universal.
apply inc_antisym.
apply inc_empty_alpha.
apply H0.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[unit\_identity\_not\_empty]
$$
id_I \neq \phi_{II}.
$$
\end{lemma}
\end{screen}
% **)
Lemma unit_identity_not_empty : Id i <> φ i i.
Proof.
move => H.
apply unit_empty_not_universal.
rewrite -H.
apply unit_identity_is_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[cupL\_emptyset]
Let $\alpha_\lambda :A \rel B$ and $E= \emptyset$. Then,
$$
\sqcup_{\lambda \in E} \alpha_\lambda = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma cupL_emptyset {A B L : eqType} {alpha_L : L -> Rel A B}:
 (L -> False) -> ∪_ alpha_L = φ A B.
Proof.
move => H.
apply inc_antisym.
apply inc_cupL.
move => l.
apply False_ind.
apply (H l).
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[capL\_emptyset]
Let $\alpha_\lambda :A \rel B$ and $E= \emptyset$. Then,
$$
\sqcap_{\lambda \in E} \alpha_\lambda = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma capL_emptyset {A B L : eqType} {alpha_L : L -> Rel A B}:
 (L -> False) -> ∩_ alpha_L = ∇ A B.
Proof.
move => H.
apply inc_antisym.
apply inc_alpha_universal.
apply inc_capL.
move => l.
apply False_ind.
apply (H l).
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cupL\_distr\_l]
Let $\alpha , \beta_\lambda :A \rel B$. Then,
$$
\alpha \sqcap (\sqcup_{\lambda \in \Lambda} \beta_\lambda) = \sqcup_{\lambda \in \Lambda} (\alpha \sqcap \beta_\lambda).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cupL_distr_l
 {A B L : eqType} {alpha : Rel A B} {beta_L : L -> Rel A B}:
 alpha ∩ (∪_ beta_L) = ∪_ (fun l : L => alpha ∩ beta_L l).
Proof.
apply inc_upper.
move => gamma.
split; move => H.
apply inc_cupL.
move => l.
apply (@inc_trans _ _ _ (alpha ∩ ∪_ beta_L)).
apply cap_inc_compat_l.
apply inc_cupL.
apply inc_refl.
apply H.
assert (forall l : L, (alpha ∩ beta_L l) ⊆ gamma).
apply inc_cupL.
apply H.
assert (forall l : L, beta_L l ⊆ (alpha >> gamma)).
move => l.
rewrite inc_rpc cap_comm.
apply H0.
rewrite cap_comm -inc_rpc.
apply inc_cupL.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cupL\_distr\_r]
Let $\alpha_\lambda , \beta :A \rel B$. Then,
$$
(\sqcup_{\lambda \in \Lambda} \alpha_\lambda) \sqcap \beta = \sqcup_{\lambda \in \Lambda} (\alpha_\lambda \sqcap \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cupL_distr_r
 {A B L : eqType} {beta : Rel A B} {alpha_L : L -> Rel A B}:
 (∪_ alpha_L) ∩ beta = ∪_ (fun l : L => alpha_L l ∩ beta).
Proof.
rewrite cap_comm.
replace (fun l : L => alpha_L l ∩ beta) with  (fun l : L => beta ∩ alpha_L l).
apply cap_cupL_distr_l.
apply functional_extensionality.
move => l.
by [rewrite cap_comm].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_capL\_distr\_l]
Let $\alpha , \beta_\lambda :A \rel B$. Then,
$$
\alpha \sqcup (\sqcap_{\lambda \in \Lambda} \beta_\lambda) = \sqcap_{\lambda \in \Lambda} (\alpha \sqcup \beta_\lambda).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_capL_distr_l
 {A B L : eqType} {alpha : Rel A B} {beta_L : L -> Rel A B}:
 alpha ∪ (∩_ beta_L) = ∩_ (fun l : L => alpha ∪ beta_L l).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capL.
move => l.
apply (@inc_trans _ _ _ (alpha ∪ ∩_ beta_L)).
apply H.
apply cup_inc_compat_l.
apply inc_capL.
apply inc_refl.
rewrite bool_lemma3.
assert (forall l : L, gamma ⊆ (alpha ∪ beta_L l)).
apply inc_capL.
apply H.
apply inc_capL.
move => l.
rewrite -bool_lemma3.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_capL\_distr\_r]
Let $\alpha_\lambda , \beta :A \rel B$. Then,
$$
(\sqcap_{\lambda \in \Lambda} \alpha_\lambda) \sqcup \beta = \sqcap_{\lambda \in \Lambda} (\alpha_\lambda \sqcup \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_capL_distr_r
 {A B L : eqType} {beta : Rel A B} {alpha_L : L -> Rel A B}:
 (∩_ alpha_L) ∪ beta = ∩_ (fun l : L => alpha_L l ∪ beta).
Proof.
rewrite cup_comm.
replace (fun l : L => alpha_L l ∪ beta) with  (fun l : L => beta ∪ alpha_L l).
apply cup_capL_distr_l.
apply functional_extensionality.
move => l.
by [rewrite cup_comm].
Qed.

(** %
\begin{screen}
\begin{lemma}[de\_morgan3]
Let $\alpha_\lambda :A \rel B$. Then,
$$
(\sqcup_{\lambda \in \Lambda} \alpha_\lambda)^- = (\sqcap_{\lambda \in \Lambda} {\alpha_\lambda}^-).
$$
\end{lemma}
\end{screen}
% **)
Lemma de_morgan3
 {A B L : eqType} {alpha_L : L -> Rel A B}:
 (∪_ alpha_L) ^ = ∩_ (fun l : L => alpha_L l ^).
Proof.
apply inc_lower.
move => gamma.
rewrite inc_capL.
split; move => H.
move => l.
rewrite bool_lemma1 -de_morgan2 complement_move complement_universal.
apply bool_lemma2 in H.
apply inc_antisym.
apply inc_empty_alpha.
rewrite -H complement_invol.
apply cap_inc_compat_l.
apply inc_cupL.
apply inc_refl.
rewrite bool_lemma2 complement_invol.
rewrite cap_cupL_distr_l.
replace (fun l : L => gamma ∩ alpha_L l) with (fun l : L => φ A B).
apply inc_antisym.
apply inc_cupL.
move => l.
apply inc_refl.
apply inc_empty_alpha.
apply functional_extensionality.
move => l.
rewrite -(@complement_invol _ _ (alpha_L l)).
apply Logic.eq_sym.
rewrite -bool_lemma2.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[de\_morgan4]
Let $\alpha_\lambda :A \rel B$. Then,
$$
(\sqcap_{\lambda \in \Lambda} \alpha_\lambda)^- = (\sqcup_{\lambda \in \Lambda} {\alpha_\lambda}^-).
$$
\end{lemma}
\end{screen}
% **)
Lemma de_morgan4
 {A B L : eqType} {alpha_L : L -> Rel A B}:
 (∩_ alpha_L) ^ = ∪_ (fun l : L => alpha_L l ^).
Proof.
rewrite -complement_move de_morgan3.
replace (fun l : L => (alpha_L l ^) ^) with alpha_L.
by [].
apply functional_extensionality.
move => l.
by [rewrite complement_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_to\_cupL, cap\_to\_capL]
We can prove $\sqcup$ and $\sqcap$ lemmas as $\sqcup_{\lambda \in \Lambda}$ and $\sqcap_{\lambda \in \Lambda}$.
\end{lemma}
\end{screen}
% **)
Lemma cup_to_cupL {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∪ beta) = ∪_ (fun b : bool_eqType => if b then alpha else beta).
Proof.
apply inc_upper.
move => gamma.
split; move => H.
apply inc_cupL.
apply inc_cup in H.
induction l.
apply H.
apply H.
apply inc_cup.
assert (forall b : bool_eqType, (fun b : bool_eqType => if b then alpha else beta) b ⊆ gamma).
apply inc_cupL.
apply H.
split.
apply (H0 true).
apply (H0 false).
Qed.

Lemma cap_to_capL {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∩ beta) = ∩_ (fun b : bool_eqType => if b then alpha else beta).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capL.
apply inc_cap in H.
induction l.
apply H.
apply H.
apply inc_cap.
assert (forall b : bool_eqType, gamma ⊆ (fun b : bool_eqType => if b then alpha else beta) b).
apply inc_capL.
apply H.
split.
apply (H0 true).
apply (H0 false).
Qed.

(** %
\section{comp\_inc\_compat と派生補題}
\begin{screen}
\begin{lemma}[comp\_inc\_compat\_ab\_ab']
Let $\alpha :A \rel B$ and $\beta , {\beta}' :B \rel C$. Then,
$$
\beta \sqsubseteq {\beta}' \Rightarrow \alpha \cdot \beta \sqsubseteq \alpha \cdot {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat_ab_ab'
 {A B C : eqType} {alpha : Rel A B} {beta beta' : Rel B C}:
 beta ⊆ beta' -> (alpha ・ beta) ⊆ (alpha ・ beta').
Proof.
move => H.
replace (alpha ・ beta) with ((alpha #) # ・ beta).
apply inc_residual.
apply (@inc_trans _ _ _ beta').
apply H.
apply inc_residual.
rewrite inv_invol.
apply inc_refl.
by [rewrite inv_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inc\_compat\_ab\_a'b]
Let $\alpha , {\alpha}' :A \rel B$ and $\beta :B \rel C$. Then,
$$
\alpha \sqsubseteq {\alpha}' \Rightarrow \alpha \cdot \beta \sqsubseteq {\alpha}' \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat_ab_a'b
 {A B C : eqType} {alpha alpha' : Rel A B} {beta : Rel B C}:
 alpha ⊆ alpha' -> (alpha ・ beta) ⊆ (alpha' ・ beta).
Proof.
move => H.
rewrite -(@inv_invol _ _ (alpha ・ beta)).
rewrite -(@inv_invol _ _ (alpha' ・ beta)).
apply inc_inv.
rewrite comp_inv comp_inv.
apply comp_inc_compat_ab_ab'.
apply inc_inv.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inc\_compat]
Let $\alpha , {\alpha}' :A \rel B$ and $\beta , {\beta}' :B \rel C$. Then,
$$
\alpha \sqsubseteq {\alpha}' \land \beta \sqsubseteq {\beta}' \Rightarrow \alpha \cdot \beta \sqsubseteq {\alpha}' \cdot {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat
 {A B C : eqType} {alpha alpha' : Rel A B} {beta beta' : Rel B C}:
 alpha ⊆ alpha' -> beta ⊆ beta' -> (alpha ・ beta) ⊆ (alpha' ・ beta').
Proof.
move => H H0.
apply (@inc_trans _ _ _ (alpha' ・ beta)).
apply (@comp_inc_compat_ab_a'b _ _ _ _ _ _ H).
apply (@comp_inc_compat_ab_ab' _ _ _ _ _ _ H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inc\_compat\_ab\_a]
Let $\alpha :A \rel B$ and $\beta :B \rel B$. Then,
$$
\beta \sqsubseteq id_B \Rightarrow \alpha \cdot \beta \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat_ab_a {A B : eqType} {alpha : Rel A B} {beta : Rel B B}:
 beta ⊆ Id B -> (alpha ・ beta) ⊆ alpha.
Proof.
move => H.
move : (@comp_inc_compat_ab_ab' _ _ _ alpha _ _ H) => H0.
rewrite comp_id_r in H0.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inc\_compat\_a\_ab]
Let $\alpha :A \rel B$ and $\beta :B \rel B$. Then,
$$
id_B \sqsubseteq \beta \Rightarrow \beta \sqsubseteq \alpha \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat_a_ab {A B : eqType} {alpha : Rel A B} {beta : Rel B B}:
 Id B ⊆ beta -> alpha ⊆ (alpha ・ beta).
Proof.
move => H.
move : (@comp_inc_compat_ab_ab' _ _ _ alpha _ _ H) => H0.
rewrite comp_id_r in H0.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inc\_compat\_ab\_b]
Let $\alpha :A \rel A$ and $\beta :A \rel B$. Then,
$$
\alpha \sqsubseteq id_A \Rightarrow \alpha \cdot \beta \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat_ab_b {A B : eqType} {alpha : Rel A A} {beta : Rel A B}:
 alpha ⊆ Id A -> (alpha ・ beta) ⊆ beta.
Proof.
move => H.
move : (@comp_inc_compat_ab_a'b _ _ _ _ _ beta H) => H0.
rewrite comp_id_l in H0.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inc\_compat\_b\_ab]
Let $\alpha :A \rel A$ and $\beta :A \rel B$. Then,
$$
id_A \sqsubseteq \alpha \Rightarrow \beta \sqsubseteq \alpha \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inc_compat_b_ab {A B : eqType} {alpha : Rel A A} {beta : Rel A B}:
 Id A ⊆ alpha -> beta ⊆ (alpha ・ beta).
Proof.
move => H.
move : (@comp_inc_compat_ab_a'b _ _ _ _ _ beta H) => H0.
rewrite comp_id_l in H0.
apply H0.
Qed.

(** %
\section{逆関係に関する補題}
\begin{screen}
\begin{lemma}[inv\_move]
Let $\alpha :A \rel B$ and $\beta :B \rel A$. Then,
$$
\alpha = \beta^\sharp \Leftrightarrow \alpha^\sharp = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_move {A B : eqType} {alpha : Rel A B} {beta : Rel B A}:
 alpha = beta # <-> alpha # = beta.
Proof.
split; move => H.
by [rewrite H inv_invol].
by [rewrite -H inv_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inv\_inv]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
\alpha \cdot \beta = (\beta^\sharp \cdot \alpha^\sharp)^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_inv_inv {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha ・ beta = (beta # ・ alpha #) #.
Proof.
apply inv_move.
apply comp_inv.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_inc\_move]
Let $\alpha :A \rel B$ and $\beta :B \rel A$. Then,
$$
\alpha \sqsubseteq \beta^\sharp \Leftrightarrow \alpha^\sharp \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_inc_move {A B : eqType} {alpha : Rel A B} {beta : Rel B A}:
 alpha ⊆ beta # <-> alpha # ⊆ beta.
Proof.
split; move => H.
rewrite -(@inv_invol _ _ beta).
apply inc_inv.
apply H.
rewrite -(@inv_invol _ _ alpha).
apply inc_inv.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_invol2]
Let $\alpha, \beta :A \rel B$. Then,
$$
\alpha^\sharp = \beta^\sharp \Rightarrow \alpha = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_invol2 {A B : eqType} {alpha beta : Rel A B}:
 alpha # = beta # -> alpha = beta.
Proof.
move => H.
rewrite -(@inv_invol _ _ alpha) -(@inv_invol _ _ beta).
apply f_equal.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_inc\_invol]
Let $\alpha, \beta :A \rel B$. Then,
$$
\alpha^\sharp \sqsubseteq \beta^\sharp \Rightarrow \alpha \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_inc_invol {A B : eqType} {alpha beta : Rel A B}:
 alpha # ⊆ beta # -> alpha ⊆ beta.
Proof.
move => H.
rewrite -(@inv_invol _ _ alpha) -(@inv_invol _ _ beta).
apply inc_inv.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_cupL\_distr, inv\_cup\_distr]
Let $\alpha_\lambda :A \rel B$. Then,
$$
(\sqcup_{\lambda \in \Lambda} \alpha_\lambda)^\sharp = (\sqcup_{\lambda \in \Lambda} {\alpha_\lambda}^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_cupL_distr {A B L : eqType} {alpha_L : L -> Rel A B}:
 (∪_ alpha_L) # = (∪_ (fun l : L => alpha_L l #)).
Proof.
apply inc_antisym.
rewrite -inv_inc_move.
apply inc_cupL.
assert (forall l : L, alpha_L l # ⊆ ∪_ (fun l0 : L => alpha_L l0 #)).
apply inc_cupL.
apply inc_refl.
move => l.
rewrite inv_inc_move.
apply H.
apply inc_cupL.
move => l.
apply inc_inv.
apply inc_cupL.
apply inc_refl.
Qed.

Lemma inv_cup_distr {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∪ beta) # = alpha # ∪ beta #.
Proof.
rewrite cup_to_cupL cup_to_cupL.
rewrite inv_cupL_distr.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_capL\_distr, inv\_cap\_distr]
Let $\alpha_\lambda :A \rel B$. Then,
$$
(\sqcap_{\lambda \in \Lambda} \alpha_\lambda)^\sharp = (\sqcap_{\lambda \in \Lambda} {\alpha_\lambda}^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_capL_distr {A B L : eqType} {alpha_L : L -> Rel A B}:
 (∩_ alpha_L) # = (∩_ (fun l : L => alpha_L l #)).
Proof.
apply inc_antisym.
apply inc_capL.
move => l.
apply inc_inv.
apply inc_capL.
apply inc_refl.
rewrite inv_inc_move.
apply inc_capL.
assert (forall l : L, ∩_ (fun l0 : L => alpha_L l0 #) ⊆ alpha_L l #).
apply inc_capL.
apply inc_refl.
move => l.
rewrite -inv_inc_move.
apply H.
Qed.

Lemma inv_cap_distr {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∩ beta) # = alpha # ∩ beta #.
Proof.
rewrite cap_to_capL cap_to_capL.
rewrite inv_capL_distr.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[rpc\_inv\_distr]
Let $\alpha, \beta :A \rel B$. Then,
$$
(\alpha \Rightarrow \beta)^\sharp = \alpha^\sharp \Rightarrow \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma rpc_inv_distr {A B : eqType} {alpha beta : Rel A B}:
 (alpha >> beta) # = alpha # >> beta #.
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_rpc.
rewrite inv_inc_move inv_cap_distr inv_invol.
rewrite -inc_rpc -inv_inc_move.
apply H.
rewrite inv_inc_move inc_rpc.
rewrite -(@inv_invol _ _ alpha) -inv_cap_distr -inv_inc_move.
apply inc_rpc.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_empty]
$$
{\phi_{AB}}^\sharp = \phi_{BA}.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_empty {A B : eqType}: φ A B # = φ B A.
Proof.
apply inc_antisym.
rewrite -inv_inc_move.
apply inc_empty_alpha.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_universal]
$$
{\nabla_{AB}}^\sharp = \nabla_{BA}.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_universal {A B : eqType}: ∇ A B # = ∇ B A.
Proof.
apply inc_antisym.
apply inc_alpha_universal.
rewrite inv_inc_move.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_id]
$$
{id_A}^\sharp = id_A.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_id {A : eqType}: (Id A) # = Id A.
Proof.
replace (Id A #) with ((Id A #) # ・ Id A #).
by [rewrite -comp_inv comp_id_l inv_invol].
by [rewrite inv_invol comp_id_l].
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_complement]
Let $\alpha :A \rel B$. Then,
$$
(\alpha^-)^\sharp = (\alpha^\sharp)^-.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_complement {A B : eqType} {alpha : Rel A B}: (alpha ^) # = (alpha #) ^.
Proof.
apply inc_antisym.
apply inc_rpc.
rewrite -inv_cap_distr.
rewrite cap_comm -inv_inc_move inv_empty.
rewrite cap_complement_empty.
apply inc_refl.
rewrite inv_inc_move.
apply inc_rpc.
replace (((alpha #) ^) # ∩ alpha) with (((alpha #) ^) # ∩ (alpha #) #).
rewrite -inv_cap_distr.
rewrite cap_comm -inv_inc_move inv_empty.
rewrite cap_complement_empty.
apply inc_refl.
by [rewrite inv_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_difference\_distr]
Let $\alpha , \beta :A \rel B$. Then,
$$
(\alpha - \beta)^\sharp = \alpha^\sharp - \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_difference_distr {A B : eqType} {alpha beta : Rel A B}:
 (alpha -- beta) # = alpha # -- beta #.
Proof.
rewrite inv_cap_distr.
by [rewrite inv_complement].
Qed.

(** %
\section{合成に関する補題}
\begin{screen}
\begin{lemma}[comp\_cupL\_distr\_l, comp\_cup\_distr\_l]
Let $\alpha :A \rel B$ and $\beta_\lambda :B \rel C$. Then,
$$
\alpha \cdot (\sqcup_{\lambda \in \Lambda} \beta_\lambda) = \sqcup_{\lambda \in \Lambda} (\alpha \cdot \beta_\lambda).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_cupL_distr_l
 {A B C L : eqType} {alpha : Rel A B} {beta_L : L -> Rel B C}:
 alpha ・ (∪_ beta_L) = ∪_ (fun l : L => (alpha ・ beta_L l)).
Proof.
apply inc_upper.
move => gamma.
split; move => H.
rewrite -(@inv_invol _ _ alpha) in H.
apply inc_residual in H.
apply inc_cupL.
assert (forall l : L, beta_L l ⊆ (alpha # △ gamma)).
apply inc_cupL.
apply H.
move => l.
rewrite -(@inv_invol _ _ alpha).
apply inc_residual.
apply H0.
rewrite -(@inv_invol _ _ alpha).
apply inc_residual.
apply inc_cupL.
assert (forall l : L, (alpha ・ beta_L l) ⊆ gamma).
apply inc_cupL.
apply H.
move => l.
apply inc_residual.
rewrite inv_invol.
apply H0.
Qed.

Lemma comp_cup_distr_l
 {A B C : eqType} {alpha : Rel A B} {beta gamma : Rel B C}:
 alpha ・ (beta ∪ gamma) = (alpha ・ beta) ∪ (alpha ・ gamma).
Proof.
rewrite cup_to_cupL cup_to_cupL.
rewrite comp_cupL_distr_l.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_cupL\_distr\_r, comp\_cup\_distr\_r]
Let $\alpha_\lambda :A \rel B$ and $\beta :B \rel C$. Then,
$$
(\sqcup_{\lambda \in \Lambda} \alpha_\lambda) \cdot \beta = \sqcup_{\lambda \in \Lambda} (\alpha_\lambda \cdot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_cupL_distr_r
 {A B C L : eqType} {alpha_L : L -> Rel A B} {beta : Rel B C}:
 (∪_ alpha_L) ・ beta = ∪_ (fun l : L => (alpha_L l ・ beta)).
Proof.
replace (fun l : L => alpha_L l ・ beta) with (fun l : L => (beta # ・ alpha_L l #) #).
rewrite -inv_cupL_distr.
rewrite -comp_cupL_distr_l.
rewrite -inv_cupL_distr.
rewrite comp_inv.
by [rewrite inv_invol inv_invol].
apply functional_extensionality.
move => l.
rewrite comp_inv.
by [rewrite inv_invol inv_invol].
Qed.

Lemma comp_cup_distr_r
 {A B C : eqType} {alpha beta : Rel A B} {gamma : Rel B C}:
 (alpha ∪ beta) ・ gamma = (alpha ・ gamma) ∪ (beta ・ gamma).
Proof.
rewrite cup_to_cupL cup_to_cupL.
rewrite comp_cupL_distr_r.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_capL\_distr]
Let $\alpha :A \rel B$, $\beta_\lambda :B \rel C$ and $\gamma :C \rel D$. Then,
$$
\alpha \cdot (\sqcap_{\lambda \in \Lambda} \beta_\lambda) \cdot \gamma \sqsubseteq \sqcap_{\lambda \in \Lambda} (\alpha \cdot \beta_\lambda \cdot \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_capL_distr {A B C D L : eqType}
 {alpha : Rel A B} {beta_L : L -> Rel B C} {gamma : Rel C D}:
 (alpha ・ (∩_ beta_L)) ・ gamma
 ⊆ ∩_ (fun l : L => ((alpha ・ beta_L l) ・ gamma)).
Proof.
apply inc_capL.
move => l.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
apply inc_capL.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_capL\_distr\_l, comp\_cap\_distr\_l]
Let $\alpha :A \rel B$, $\beta_\lambda :B \rel C$. Then,
$$
\alpha \cdot (\sqcap_{\lambda \in \Lambda} \beta_\lambda) \sqsubseteq \sqcap_{\lambda \in \Lambda} (\alpha \cdot \beta_\lambda).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_capL_distr_l
 {A B C L : eqType} {alpha : Rel A B} {beta_L : L -> Rel B C}:
 (alpha ・ (∩_ beta_L)) ⊆ ∩_ (fun l : L => (alpha ・ beta_L l)).
Proof.
move : (@comp_capL_distr _ _ _ _ _ alpha beta_L (Id C)) => H.
rewrite comp_id_r in H.
replace (fun l : L => (alpha ・ beta_L l) ・ Id C) with (fun l : L => (alpha ・ beta_L l)) in H.
apply H.
apply functional_extensionality.
move => l.
by [rewrite comp_id_r].
Qed.

Lemma comp_cap_distr_l
 {A B C : eqType} {alpha : Rel A B} {beta gamma : Rel B C}:
 (alpha ・ (beta ∩ gamma)) ⊆ ((alpha ・ beta) ∩ (alpha ・ gamma)).
Proof.
rewrite cap_to_capL cap_to_capL.
apply (@inc_trans _ _ _ _ _ comp_capL_distr_l).
replace (∩_ (fun l : bool_eqType => alpha ・ (if l then beta else gamma))) with (∩_ (fun b : bool_eqType => if b then alpha ・ beta else alpha ・ gamma)).
apply inc_refl.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_capL\_distr\_r, comp\_cap\_distr\_r]
Let $\alpha_\lambda :A \rel B$, $\beta :B \rel C$. Then,
$$
(\sqcap_{\lambda \in \Lambda} \alpha_\lambda) \cdot \beta \sqsubseteq \sqcap_{\lambda \in \Lambda} (\alpha_\lambda \cdot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_capL_distr_r
 {A B C L : eqType} {beta : Rel B C} {alpha_L : L -> Rel A B}:
 ((∩_ alpha_L) ・ beta) ⊆ ∩_ (fun l : L => (alpha_L l ・ beta)).
Proof.
move : (@comp_capL_distr _ _ _ _ _ (Id A) alpha_L beta) => H.
rewrite comp_id_l in H.
replace (fun l : L => (Id A ・ alpha_L l) ・ beta) with (fun l : L => alpha_L l ・ beta) in H.
apply H.
apply functional_extensionality.
move => l.
by [rewrite comp_id_l].
Qed.

Lemma comp_cap_distr_r
 {A B C : eqType} {alpha beta : Rel A B} {gamma : Rel B C}:
 ((alpha ∩ beta) ・ gamma) ⊆ ((alpha ・ gamma) ∩ (beta ・ gamma)).
Proof.
rewrite cap_to_capL cap_to_capL.
apply (@inc_trans _ _ _ _ _ comp_capL_distr_r).
replace (∩_ (fun l : bool_eqType => (if l then alpha else beta) ・ gamma)) with (∩_ (fun b : bool_eqType => if b then alpha ・ gamma else beta ・ gamma)).
apply inc_refl.
apply f_equal.
apply functional_extensionality.
induction x.
by [].
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_empty\_l, comp\_empty\_r]
Let $\alpha :A \rel B$, $\beta :B \rel C$. Then,
$$
\alpha \cdot \phi_{BC} = \phi_{AB} \cdot \beta = \phi_{AC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_empty_r {A B C : eqType} {alpha : Rel A B}: alpha ・ φ B C = φ A C.
Proof.
apply inc_antisym.
rewrite -(@inv_invol _ _ alpha).
apply inc_residual.
apply inc_empty_alpha.
apply inc_empty_alpha.
Qed.

Lemma comp_empty_l {A B C : eqType} {beta : Rel B C}: φ A B ・ beta = φ A C.
Proof.
rewrite -(@inv_invol _ _ (φ A B ・ beta)).
rewrite -inv_move comp_inv inv_empty inv_empty.
apply comp_empty_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_either\_empty]
Let $\alpha :A \rel B$, $\beta :B \rel C$. Then,
$$
\alpha = \phi_{AB} \lor \beta = \phi_{BC} \Rightarrow \alpha \cdot \beta = \phi_{AC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_either_empty {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha = φ A B \/ beta = φ B C -> alpha ・ beta = φ A C.
Proof.
case; move => H.
rewrite H.
apply comp_empty_l.
rewrite H.
apply comp_empty_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_neither\_empty]
Let $\alpha :A \rel B$, $\beta :B \rel C$. Then,
$$
\alpha \cdot \beta \neq \phi_{AC} \Rightarrow \alpha \neq \phi_{AB} \land \beta \neq \phi_{BC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_neither_empty {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha ・ beta <> φ A C -> alpha <> φ A B /\ beta <> φ B C.
Proof.
move => H.
split; move => H0.
apply H.
rewrite H0.
apply comp_empty_l.
apply H.
rewrite H0.
apply comp_empty_r.
Qed.

(** %
\section{単域と Tarski の定理}
\begin{screen}
\begin{lemma}[lemma\_for\_tarski1]
Let $\alpha :A \rel B$ and $\alpha \neq \phi_{AB}$. Then,
$$
\nabla_{IA} \cdot \alpha \cdot \nabla_{BI} = id_I.
$$
\end{lemma}
\end{screen}
% **)
Lemma lemma_for_tarski1 {A B : eqType} {alpha : Rel A B}:
 alpha <> φ A B -> ((∇ i A ・ alpha) ・ ∇ B i) = Id i.
Proof.
move => H.
assert (((∇ i A ・ alpha) ・ ∇ B i) <> φ i i).
move => H0.
apply H.
apply inc_antisym.
apply (@inc_trans _ _ _ ((∇ A i ・ ((∇ i A ・ alpha) ・ ∇ B i)) ・ ∇ i B)).
rewrite comp_assoc comp_assoc unit_universal.
rewrite -comp_assoc -comp_assoc unit_universal.
apply (@inc_trans _ _ _ ((Id A ・ alpha) ・ Id B)).
rewrite comp_id_l comp_id_r.
apply inc_refl.
apply comp_inc_compat.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
apply inc_alpha_universal.
rewrite H0 comp_empty_r comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
case (@unit_empty_or_universal ((∇ i A ・ alpha) ・ ∇ B i)); move => H1.
apply False_ind.
apply (H0 H1).
rewrite unit_identity_is_universal.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[lemma\_for\_tarski2]
$$
\nabla_{AI} \cdot \nabla_{IB} = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma lemma_for_tarski2 {A B : eqType}: ∇ A i ・ ∇ i B = ∇ A B.
Proof.
apply inc_antisym.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ (∇ A A ・ ∇ A B)).
apply (@inc_trans _ _ _ (Id A ・ ∇ A B)).
rewrite comp_id_l.
apply inc_refl.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
rewrite -(@unit_universal A) comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[tarski]
Let $\alpha :A \rel B$ and $\alpha \neq \phi_{AB}$. Then,
$$
\nabla_{AA} \cdot \alpha \cdot \nabla_{BB} = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma tarski {A B : eqType} {alpha : Rel A B}:
 alpha <> φ A B -> ((∇ A A ・ alpha) ・ ∇ B B) = ∇ A B.
Proof.
move => H.
rewrite -(@unit_universal A) -(@unit_universal B).
move : (@lemma_for_tarski1 _ _ alpha H) => H0.
rewrite -comp_assoc (@comp_assoc _ _ _ _ (∇ A i)) (@comp_assoc _ _ _ _ (∇ A i)).
rewrite H0 comp_id_r.
apply lemma_for_tarski2.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_universal1]
Let $B \neq \emptyset$. Then,
$$
\nabla_{AB} \cdot \nabla_{BC} = \nabla_{AC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_universal {A B C : eqType} : B -> ∇ A B ・ ∇ B C = ∇ A C.
Proof.
move => b.
replace (∇ A B) with (∇ A B ・ ∇ B B).
rewrite -(@lemma_for_tarski2 A B) -(@lemma_for_tarski2 B C).
rewrite (@comp_assoc _ _ _ _ (∇ A i)) (@comp_assoc _ _ _ _ (∇ A i)) -(@comp_assoc _ _ _ _ _ (∇ B i)).
rewrite lemma_for_tarski1.
rewrite comp_id_l.
apply lemma_for_tarski2.
apply not_eq_sym.
move => H.
apply either_empty in H.
case H; move => H0.
apply (H0 b).
apply (H0 b).
apply inc_antisym.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ (∇ A B ・ Id B)).
rewrite comp_id_r.
apply inc_refl.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_universal2]
$$
{\nabla_{IA}}^\sharp \cdot \nabla_{IB} = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_universal2 {A B : eqType}: ∇ i A # ・ ∇ i B = ∇ A B.
Proof.
rewrite inv_universal.
apply lemma_for_tarski2.
Qed.

(** %
\begin{screen}
\begin{lemma}[empty\_equivalence1, empty\_equivalence2, empty\_equivalence3]
$$
A = \emptyset \Leftrightarrow \nabla_{IA} = \phi_{IA} \Leftrightarrow \nabla_{AA} = \phi_{AA} \Leftrightarrow id_A = \phi_{AA}.
$$
\end{lemma}
\end{screen}
% **)
Lemma empty_equivalence1 {A : eqType}: (A -> False) <-> ∇ i A = φ i A.
Proof.
move : (@either_empty i A) => H.
split; move => H0.
apply Logic.eq_sym.
apply H.
right.
apply H0.
apply Logic.eq_sym in H0.
apply H in H0.
case H0.
move => H1 H2.
apply H1.
apply tt.
by [].
Qed.

Lemma empty_equivalence2 {A : eqType}: (A -> False) <-> ∇ A A = φ A A.
Proof.
move : (@either_empty A A) => H.
split; move => H0.
apply Logic.eq_sym.
apply H.
left.
apply H0.
apply Logic.eq_sym in H0.
apply H in H0.
case H0.
by [].
by [].
Qed.

Lemma empty_equivalence3 {A : eqType}: (A -> False) <-> Id A = φ A A.
Proof.
split; move => H.
assert (∇ A A = φ A A).
apply empty_equivalence2.
apply H.
apply RelAB_unique.
apply Logic.eq_sym.
apply H0.
assert (φ A A = ∇ A A).
by [rewrite -(@comp_id_r _ _ (∇ A A)) H comp_empty_r].
apply either_empty in H0.
case H0.
by [].
by [].
Qed.