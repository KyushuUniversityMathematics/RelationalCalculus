Require Import Basic_Notations_Set.
Require Import Basic_Lemmas.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.Classical_Prop.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Import Basic_Lemmas.

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
\begin{lemma}[cupP\_False]
Let $f:(C \rel D) \to (A \rel B)$ and $P(\alpha):=$ ``False''. Then,
$$
\sqcup_{P(\alpha)} f(\alpha) = \phi_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma cupP_False {A B C D : eqType} {f : Rel C D -> Rel A B}:
 ∪_{fun _ : Rel C D => False} f = φ A B.
Proof.
apply inc_antisym.
apply inc_cupP.
move => beta.
apply False_ind.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[capP\_False]
Let $f:(C \rel D) \to (A \rel B)$ and $P(\alpha):=$ ``False''. Then,
$$
\sqcap_{P(\alpha)} f(\alpha) = \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Lemma capP_False {A B C D : eqType} {f : Rel C D -> Rel A B}:
 ∩_{fun _ : Rel C D => False} f = ∇ A B.
Proof.
apply inc_antisym.
apply inc_alpha_universal.
apply inc_capP.
move => beta.
apply False_ind.
Qed.

(** %
\begin{screen}
\begin{lemma}[cupP\_eq]
Let $f,g:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\forall \alpha :C \rel D, P(\alpha) \Rightarrow f(\alpha) = g(\alpha)) \Rightarrow \sqcup_{P(\alpha)} f(\alpha) = \sqcup_{P(\alpha)} g(\alpha).
$$
\end{lemma}
\end{screen}
% **)
Lemma cupP_eq {A B C D : eqType}
 {f g : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (forall alpha : Rel C D, P alpha -> f alpha = g alpha) -> ∪_{P} f = ∪_{P} g.
Proof.
move => H.
apply inc_antisym.
apply inc_cupP.
move => beta H0.
rewrite (H _ H0).
move : beta H0.
apply inc_cupP.
apply inc_refl.
apply inc_cupP.
move => beta H0.
rewrite -(H _ H0).
move : beta H0.
apply inc_cupP.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[capP\_eq]
Let $f,g:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\forall \alpha :C \rel D, P(\alpha) \Rightarrow f(\alpha) = g(\alpha)) \Rightarrow \sqcap_{P(\alpha)} f(\alpha) = \sqcap_{P(\alpha)} g(\alpha).
$$
\end{lemma}
\end{screen}
% **)
Lemma capP_eq {A B C D : eqType}
 {f g : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (forall alpha : Rel C D, P alpha -> f alpha = g alpha) -> ∩_{P} f = ∩_{P} g.
Proof.
move => H.
apply inc_antisym.
apply inc_capP.
move => beta H0.
rewrite -(H _ H0).
move : beta H0.
apply inc_capP.
apply inc_refl.
apply inc_capP.
move => beta H0.
rewrite (H _ H0).
move : beta H0.
apply inc_capP.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cupP\_distr\_l]
Let $\alpha :A \rel B$, $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
\alpha \sqcap (\sqcup_{P(\beta)} f(\beta)) = \sqcup_{P(\beta)} (\alpha \sqcap f(\beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cupP_distr_l {A B C D : eqType}
 {alpha : Rel A B} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 alpha ∩ (∪_{P} f) = ∪_{P} (fun beta : Rel C D => alpha ∩ f beta).
Proof.
apply inc_upper.
move => gamma.
split; move => H.
apply inc_cupP.
move => beta H0.
apply (@inc_trans _ _ _ (alpha ∩ ∪_{P} f)).
apply cap_inc_compat_l.
move : H0.
apply inc_cupP.
apply inc_refl.
apply H.
assert (forall beta : Rel C D, P beta -> (alpha ∩ f beta) ⊆ gamma).
apply inc_cupP.
apply H.
assert (forall beta : Rel C D, P beta -> f beta ⊆ (alpha >> gamma)).
move => beta H1.
rewrite inc_rpc cap_comm.
apply (H0 _ H1).
rewrite cap_comm -inc_rpc.
apply inc_cupP.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_cupP\_distr\_r]
Let $\beta :A \rel B$, $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcup_{P(\alpha)} f(\alpha)) \sqcap \beta = \sqcup_{P(\alpha)} (f(\alpha) \sqcap \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_cupP_distr_r {A B C D : eqType}
 {beta : Rel A B} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (∪_{P} f) ∩ beta = ∪_{P} (fun alpha : Rel C D => f alpha ∩ beta).
Proof.
rewrite cap_comm.
replace (fun alpha : Rel C D => f alpha ∩ beta) with  (fun alpha : Rel C D => beta ∩ f alpha).
apply cap_cupP_distr_l.
apply functional_extensionality.
move => x.
by [rewrite cap_comm].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_capP\_distr\_l]
Let $\alpha :A \rel B$, $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
\alpha \sqcup (\sqcap_{P(\beta)} f(\beta)) = \sqcap_{P(\beta)} (\alpha \sqcup f(\beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_capP_distr_l {A B C D : eqType}
 {alpha : Rel A B} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 alpha ∪ (∩_{P} f) = ∩_{P} (fun beta : Rel C D => alpha ∪ f beta).
Proof.
apply inc_lower.
move => gamma.
split; move => H.
apply inc_capP.
move => beta H0.
apply (@inc_trans _ _ _ (alpha ∪ ∩_{P} f)).
apply H.
apply cup_inc_compat_l.
move : H0.
apply inc_capP.
apply inc_refl.
rewrite bool_lemma3.
assert (forall beta : Rel C D, P beta -> gamma ⊆ (alpha ∪ f beta)).
apply inc_capP.
apply H.
apply inc_capP.
move => beta H1.
rewrite -bool_lemma3.
apply (H0 _ H1).
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_capP\_distr\_r]
Let $\beta :A \rel B$, $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcap_{P(\alpha)} f(\alpha)) \sqcup \beta = \sqcap_{P(\alpha)} (f(\alpha) \sqcup \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_capP_distr_r {A B C D : eqType}
 {beta : Rel A B} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (∩_{P} f) ∪ beta = ∩_{P} (fun alpha : Rel C D => f alpha ∪ beta).
Proof.
rewrite cup_comm.
replace (fun alpha : Rel C D => f alpha ∪ beta) with  (fun alpha : Rel C D => beta ∪ f alpha).
apply cup_capP_distr_l.
apply functional_extensionality.
move => x.
by [rewrite cup_comm].
Qed.

(** %
\begin{screen}
\begin{lemma}[de\_morgan3]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcup_{P(\alpha)} f(\alpha))^- = (\sqcap_{P(\alpha)} f(\alpha)^-).
$$
\end{lemma}
\end{screen}
% **)
Lemma de_morgan3
 {A B C D : eqType} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (∪_{P} f) ^ = ∩_{P} (fun alpha : Rel C D => f alpha ^).
Proof.
apply inc_lower.
move => gamma.
rewrite inc_capP.
split; move => H.
move => beta H0.
rewrite bool_lemma1 -de_morgan2 complement_move complement_universal.
apply bool_lemma2 in H.
apply inc_antisym.
apply inc_empty_alpha.
rewrite -H complement_invol.
apply cap_inc_compat_l.
move : H0.
apply inc_cupP.
apply inc_refl.
rewrite bool_lemma2 complement_invol.
rewrite cap_cupP_distr_l.
apply inc_antisym.
apply inc_cupP.
move => beta H0.
rewrite -inc_rpc.
apply (H _ H0).
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[de\_morgan4]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcap_{P(\alpha)} f(\alpha))^- = (\sqcup_{P(\alpha)} f(\alpha)^-).
$$
\end{lemma}
\end{screen}
% **)
Lemma de_morgan4
 {A B C D : eqType} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (∩_{P} f) ^ = ∪_{P} (fun alpha : Rel C D => f alpha ^).
Proof.
rewrite -complement_move de_morgan3.
replace (fun alpha : Rel C D => (f alpha ^) ^) with f.
by [].
apply functional_extensionality.
move => x.
by [rewrite complement_invol].
Qed.

(** %
\begin{screen}
\begin{lemma}[cup\_to\_cupP]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
f(\alpha) \sqcup f(\beta) = \sqcup_{\gamma = \alpha \lor \gamma = \beta} f(\gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cup_to_cupP
 {A B C D : eqType} {alpha beta : Rel C D} {f : Rel C D -> Rel A B}:
 (f alpha ∪ f beta) = ∪_{fun gamma : Rel C D => gamma = alpha \/ gamma = beta} f.
Proof.
apply inc_upper.
move => delta.
split; move => H.
apply inc_cupP.
apply inc_cup in H.
move => gamma H0.
case H0 => H1.
rewrite H1.
apply H.
rewrite H1.
apply H.
apply inc_cup.
assert (forall gamma : Rel C D, gamma = alpha \/ gamma = beta -> f gamma ⊆ delta).
apply inc_cupP.
apply H.
split.
apply (H0 alpha).
by [left].
apply (H0 beta).
by [right].
Qed.

(** %
\begin{screen}
\begin{lemma}[cap\_to\_capP]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
f(\alpha) \sqcap f(\beta) = \sqcap_{\gamma = \alpha \lor \gamma = \beta} f(\gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_to_capP
 {A B C D : eqType} {alpha beta : Rel C D} {f : Rel C D -> Rel A B}:
 (f alpha ∩ f beta) = ∩_{fun gamma : Rel C D => gamma = alpha \/ gamma = beta} f.
Proof.
apply inc_lower.
move => delta.
split; move => H.
apply inc_capP.
apply inc_cap in H.
move => gamma H0.
case H0 => H1.
rewrite H1.
apply H.
rewrite H1.
apply H.
apply inc_cap.
assert (forall gamma : Rel C D, gamma = alpha \/ gamma = beta -> delta ⊆ f gamma).
apply inc_capP.
apply H.
split.
apply (H0 alpha).
by [left].
apply (H0 beta).
by [right].
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
\begin{lemma}[inv\_cupP\_distr, inv\_cup\_distr]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcup_{P(\alpha)} f(\alpha))^\sharp = (\sqcup_{P(\alpha)} f(\alpha)^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_cupP_distr {A B C D : eqType} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (∪_{P} f) # = (∪_{P} (fun alpha : Rel C D => f alpha #)).
Proof.
apply inc_antisym.
rewrite -inv_inc_move.
apply inc_cupP.
assert (forall beta : Rel C D, P beta -> f beta # ⊆ ∪_{P} (fun alpha : Rel C D => f alpha #)).
apply inc_cupP.
apply inc_refl.
move => beta H0.
rewrite inv_inc_move.
apply (H _ H0).
apply inc_cupP.
move => beta H0.
apply inc_inv.
move : H0.
apply inc_cupP.
apply inc_refl.
Qed.

Lemma inv_cup_distr {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∪ beta) # = alpha # ∪ beta #.
Proof.
by [rewrite cup_to_cupP -inv_cupP_distr -cup_to_cupP].
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_capP\_distr, inv\_cap\_distr]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcap_{P(\alpha)} f(\alpha))^\sharp = (\sqcap_{P(\alpha)} f(\alpha)^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_capP_distr {A B C D : eqType} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (∩_{P} f) # = (∩_{P} (fun alpha : Rel C D => f alpha #)).
Proof.
apply inc_antisym.
apply inc_capP.
move => beta H.
apply inc_inv.
move : H.
apply inc_capP.
apply inc_refl.
rewrite inv_inc_move.
apply inc_capP.
assert (forall beta : Rel C D, P beta -> ∩_{P} (fun alpha : Rel C D => f alpha #) ⊆ f beta #).
apply inc_capP.
apply inc_refl.
move => beta H0.
rewrite -inv_inc_move.
apply (H _ H0).
Qed.

Lemma inv_cap_distr {A B : eqType} {alpha beta : Rel A B}:
 (alpha ∩ beta) # = alpha # ∩ beta #.
Proof.
by [rewrite cap_to_capP -inv_capP_distr -cap_to_capP].
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
\begin{lemma}[comp\_cupP\_distr\_l, comp\_cup\_distr\_l]
Let $\alpha :A \rel B$, $f:(D \rel E) \to (B \rel C)$ and $P$ : predicate. Then,
$$
\alpha \cdot (\sqcup_{P(\beta)} f(\beta)) = \sqcup_{P(\beta)} (\alpha \cdot f(\beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_cupP_distr_l {A B C D E : eqType}
 {alpha : Rel A B} {f : Rel D E -> Rel B C} {P : Rel D E -> Prop}:
 alpha ・ (∪_{P} f) = ∪_{P} (fun beta : Rel D E => (alpha ・ f beta)).
Proof.
apply inc_upper.
move => gamma.
split; move => H.
rewrite -(@inv_invol _ _ alpha) in H.
apply inc_residual in H.
apply inc_cupP.
assert (forall beta : Rel D E, P beta -> f beta ⊆ (alpha # △ gamma)).
apply inc_cupP.
apply H.
move => beta H1.
rewrite -(@inv_invol _ _ alpha).
apply inc_residual.
apply (H0 _ H1).
rewrite -(@inv_invol _ _ alpha).
apply inc_residual.
apply inc_cupP.
assert (forall beta : Rel D E, P beta -> (alpha ・ f beta) ⊆ gamma).
apply inc_cupP.
apply H.
move => beta H1.
apply inc_residual.
rewrite inv_invol.
apply (H0 _ H1).
Qed.

Lemma comp_cup_distr_l
 {A B C : eqType} {alpha : Rel A B} {beta gamma : Rel B C}:
 alpha ・ (beta ∪ gamma) = (alpha ・ beta) ∪ (alpha ・ gamma).
Proof.
by [rewrite cup_to_cupP -comp_cupP_distr_l -cup_to_cupP].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_cupP\_distr\_r, comp\_cup\_distr\_r]
Let $f:(D \rel E) \to (A \rel B)$, $\beta :B \rel C$ and $P$ : predicate. Then,
$$
(\sqcup_{P(\alpha)} f(\alpha)) \cdot \beta = \sqcup_{P(\alpha)} (f(\alpha) \cdot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_cupP_distr_r {A B C D E : eqType}
 {beta : Rel B C} {f : Rel D E -> Rel A B} {P : Rel D E -> Prop}:
 (∪_{P} f) ・ beta = ∪_{P} (fun alpha : Rel D E => (f alpha ・ beta)).
Proof.
replace (fun alpha : Rel D E => f alpha ・ beta) with (fun alpha : Rel D E => (beta # ・ f alpha #) #).
rewrite -inv_cupP_distr.
rewrite -comp_cupP_distr_l.
rewrite -inv_cupP_distr.
rewrite comp_inv.
by [rewrite inv_invol inv_invol].
apply functional_extensionality.
move => x.
rewrite comp_inv.
by [rewrite inv_invol inv_invol].
Qed.

Lemma comp_cup_distr_r
 {A B C : eqType} {alpha beta : Rel A B} {gamma : Rel B C}:
 (alpha ∪ beta) ・ gamma = (alpha ・ gamma) ∪ (beta ・ gamma).
Proof.
by [rewrite (@cup_to_cupP _ _ _ _ _ _ id) comp_cupP_distr_r -cup_to_cupP].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_capP\_distr]
Let $\alpha :A \rel B$, $\gamma :C \rel D$, $f:(E \rel F) \to (B \rel C)$ and $P$ : predicate. Then,
$$
\alpha \cdot (\sqcap_{P(\beta)} f(\beta)) \cdot \gamma \sqsubseteq \sqcap_{P(\beta)} (\alpha \cdot f(\beta) \cdot \gamma).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_capP_distr {A B C D E F : eqType}
 {alpha : Rel A B} {gamma : Rel C D}
 {f : Rel E F -> Rel B C} {P : Rel E F -> Prop}:
 (alpha ・ (∩_{P} f)) ・ gamma
 ⊆ ∩_{P} (fun beta : Rel E F => ((alpha ・ f beta) ・ gamma)).
Proof.
apply inc_capP.
move => beta H.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
move : H.
apply inc_capP.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_capP\_distr\_l, comp\_cap\_distr\_l]
Let $\alpha :A \rel B$, $f:(D \rel E) \to (B \rel C)$ and $P$ : predicate. Then,
$$
\alpha \cdot (\sqcap_{P(\beta)} f(\beta)) \sqsubseteq \sqcap_{P(\beta)} (\alpha \cdot f(\beta)).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_capP_distr_l {A B C D E : eqType}
 {alpha : Rel A B} {f : Rel D E -> Rel B C} {P : Rel D E -> Prop}:
 (alpha ・ (∩_{P} f)) ⊆ ∩_{P} (fun beta : Rel D E => (alpha ・ f beta)).
Proof.
move : (@comp_capP_distr _ _ _ _ _ _ alpha (Id C) f P) => H.
rewrite comp_id_r in H.
replace (fun beta : Rel D E => (alpha ・ f beta) ・ Id C) with (fun beta : Rel D E => (alpha ・ f beta)) in H.
apply H.
apply functional_extensionality.
move => x.
by [rewrite comp_id_r].
Qed.

Lemma comp_cap_distr_l
 {A B C : eqType} {alpha : Rel A B} {beta gamma : Rel B C}:
 (alpha ・ (beta ∩ gamma)) ⊆ ((alpha ・ beta) ∩ (alpha ・ gamma)).
Proof.
rewrite cap_to_capP (@cap_to_capP _ _ _ _ _ _ id).
apply comp_capP_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_capP\_distr\_r, comp\_cap\_distr\_r]
Let $\beta :B \rel C$, $f:(D \rel E) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcap_{P(\alpha)} f(\alpha)) \cdot \beta \sqsubseteq \sqcap_{P(\alpha)} (f(\alpha) \cdot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_capP_distr_r
 {A B C D E : eqType} {beta : Rel B C} {f : Rel D E -> Rel A B} {P : Rel D E -> Prop}:
 ((∩_{P} f) ・ beta) ⊆ ∩_{P} (fun alpha : Rel D E => (f alpha ・ beta)).
Proof.
move : (@comp_capP_distr _ _ _ _ _ _ (Id A) beta f P) => H.
rewrite comp_id_l in H.
replace (fun alpha : Rel D E => (Id A ・ f alpha) ・ beta) with (fun alpha : Rel D E => f alpha ・ beta) in H.
apply H.
apply functional_extensionality.
move => x.
by [rewrite comp_id_l].
Qed.

Lemma comp_cap_distr_r
 {A B C : eqType} {alpha beta : Rel A B} {gamma : Rel B C}:
 ((alpha ∩ beta) ・ gamma) ⊆ ((alpha ・ gamma) ∩ (beta ・ gamma)).
Proof.
rewrite (@cap_to_capP _ _ _ _ _ _ id) (@cap_to_capP _ _ _ _ _ _ (fun x => x ・ gamma)).
apply comp_capP_distr_r.
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

End main.