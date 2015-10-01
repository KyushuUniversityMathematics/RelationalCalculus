Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Conjugate.
Require Import Domain.
Require Import Logic.IndefiniteDescription.

(** %
\section{関係の直和}
\subsection{入射対, 関係直和の定義}
\begin{screen}
入射対の存在公理(Axiom 23)で入射対が存在することまでは仮定済みなので, 実際に入射対 $j:A \rel A+B,k:B \rel A+B$ を定義する関数を定義する.
\end{screen}
% **)
Definition sum_r (A B : eqType):
 {x : (Rel A (sum_eqType A B)) * (Rel B (sum_eqType A B)) |
 (fst x) ・ (fst x) # = Id A /\ (snd x) ・ (snd x) # = Id B /\
 (fst x) ・ (snd x) # = φ A B /\
 ((fst x) # ・ (fst x)) ∪ ((snd x) # ・ (snd x)) = Id (sum_eqType A B)}.
apply constructive_indefinite_description.
elim (@pair_of_inclusions A B) => j.
elim => k H.
exists (j,k).
simpl.
apply H.
Defined.
Definition inl_r (A B : eqType):= fst (sval (sum_r A B)).
Definition inr_r (A B : eqType):= snd (sval (sum_r A B)).

(** %
\begin{screen}
またこの定義による入射対が, 入射対としての性質(Axiom 23) $+ \alpha$ を満たしていることも事前に証明しておく.
\end{screen}
% **)
Lemma inl_id {A B : eqType}: inl_r A B ・ inl_r A B # = Id A.
Proof.
apply (proj2_sig (sum_r A B)).
Qed.
Lemma inr_id {A B : eqType}: inr_r A B ・ inr_r A B # = Id B.
Proof.
apply (proj2_sig (sum_r A B)).
Qed.
Lemma inl_inr_empty {A B : eqType}: inl_r A B ・ inr_r A B # = φ A B.
Proof.
apply (proj2_sig (sum_r A B)).
Qed.
Lemma inr_inl_empty {A B : eqType}: inr_r A B ・ inl_r A B # = φ B A.
Proof.
apply inv_invol2.
rewrite comp_inv inv_invol inv_empty.
apply inl_inr_empty.
Qed.
Lemma inl_inr_cup_id {A B : eqType}:
 (inl_r A B # ・ inl_r A B) ∪ (inr_r A B # ・ inr_r A B) = Id (sum_eqType A B).
Proof.
apply (proj2_sig (sum_r A B)).
Qed.
Lemma inl_function {A B : eqType}: function_r (inl_r A B).
Proof.
move : (proj2_sig (sum_r A B)).
elim => H.
elim => H0.
elim => H1 H2.
split.
rewrite /total_r.
rewrite H.
apply inc_refl.
rewrite /univalent_r.
rewrite -H2.
apply cup_l.
Qed.
Lemma inr_function {A B : eqType}: function_r (inr_r A B).
Proof.
move : (proj2_sig (sum_r A B)).
elim => H.
elim => H0.
elim => H1 H2.
split.
rewrite /total_r.
rewrite H0.
apply inc_refl.
rewrite /univalent_r.
rewrite -H2.
apply cup_r.
Qed.

(** %
\begin{screen}
さらに $\alpha :A \rel C$ と $\beta :B \rel C$ の関係直和 $\alpha \bot \beta :A+B \rel C$ を, $\alpha \bot \beta := j^\sharp \cdot \alpha \sqcup k^\sharp \cdot \beta$ で定義する.
\end{screen}
% **)
Definition Rel_sum {A B C : eqType} (alpha : Rel A C) (beta : Rel B C):=
 (inl_r A B # ・ alpha) ∪ (inr_r A B # ・ beta).

(** %
\subsection{関係直和の性質}
\begin{screen}
\begin{lemma}[sum\_inc\_compat]
Let $\alpha, {\alpha}' :A \rel C$ and $\beta, {\beta}' :B \rel C$. Then,
$$
\alpha \sqsubseteq {\alpha}' \land \beta \sqsubseteq {\beta}' \Rightarrow \alpha \bot \beta \sqsubseteq {\alpha}' \bot {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_inc_compat
 {A B C : eqType} {alpha alpha' : Rel A C} {beta beta' : Rel B C}:
 alpha ⊆ alpha' -> beta ⊆ beta' -> Rel_sum alpha beta ⊆ Rel_sum alpha' beta'.
Proof.
move => H H0.
apply cup_inc_compat.
apply (comp_inc_compat_ab_ab' H).
apply (comp_inc_compat_ab_ab' H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_inc\_compat\_l]
Let $\alpha :A \rel C$ and $\beta, {\beta}' :B \rel C$. Then,
$$
\beta \sqsubseteq {\beta}' \Rightarrow \alpha \bot \beta \sqsubseteq \alpha \bot {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_inc_compat_l
 {A B C : eqType} {alpha : Rel A C} {beta beta' : Rel B C}:
 beta ⊆ beta' -> Rel_sum alpha beta ⊆ Rel_sum alpha beta'.
Proof.
move => H.
apply (sum_inc_compat (@inc_refl _ _ alpha) H).
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_inc\_compat\_r]
Let $\alpha, {\alpha}' :A \rel C$ and $\beta :B \rel C$. Then,
$$
\alpha \sqsubseteq {\alpha}' \Rightarrow \alpha \bot \beta \sqsubseteq {\alpha}' \bot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_inc_compat_r
 {A B C : eqType} {alpha alpha' : Rel A C} {beta : Rel B C}:
 alpha ⊆ alpha' -> Rel_sum alpha beta ⊆ Rel_sum alpha' beta.
Proof.
move => H.
apply (sum_inc_compat H (@inc_refl _ _ beta)).
Qed.

(** %
\begin{screen}
\begin{lemma}[total\_sum]
Let $\alpha :A \rel C$ and $\beta :B \rel C$ are total relations, then $\alpha \bot \beta$ is also a total relation.
\end{lemma}
\end{screen}
% **)
Lemma total_sum {A B C : eqType} {alpha : Rel A C} {beta : Rel B C}:
 total_r alpha -> total_r beta -> total_r (Rel_sum alpha beta).
Proof.
move => H H0.
rewrite /total_r/Rel_sum.
rewrite -inl_inr_cup_id inv_cup_distr comp_cup_distr_l comp_cup_distr_r comp_cup_distr_r.
rewrite comp_inv comp_inv inv_invol inv_invol.
apply cup_inc_compat.
apply (fun H' => @inc_trans _ _ _ _ _ H' (cup_l)).
rewrite comp_assoc -(@comp_assoc _ _ _ _ alpha).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H).
apply (fun H' => @inc_trans _ _ _ _ _ H' (cup_r)).
rewrite comp_assoc -(@comp_assoc _ _ _ _ beta).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[univalent\_sum]
Let $\alpha :A \rel C$ and $\beta :B \rel C$ are univalent relations, then $\alpha \bot \beta$ is also a univalent relation.
\end{lemma}
\end{screen}
% **)
Lemma univalent_sum {A B C : eqType} {alpha : Rel A C} {beta : Rel B C}:
 univalent_r alpha -> univalent_r beta -> univalent_r (Rel_sum alpha beta).
Proof.
move => H H0.
rewrite /univalent_r/Rel_sum.
rewrite inv_cup_distr comp_cup_distr_l comp_cup_distr_r comp_cup_distr_r.
rewrite comp_inv comp_inv inv_invol inv_invol.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (inl_r A B)) inl_id comp_id_l.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (inr_r A B)) inr_inl_empty comp_empty_l comp_empty_r cup_empty.
rewrite -cup_assoc comp_assoc -(@comp_assoc _ _ _ _ (inl_r A B)) inl_inr_empty comp_empty_l comp_empty_r cup_empty.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (inr_r A B)) inr_id comp_id_l.
apply inc_cup.
split.
apply H.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_sum]
Let $\alpha :A \to C$ and $\beta :B \to C$ are functions, then $\alpha \bot \beta$ is also a function.
\end{lemma}
\end{screen}
% **)
Lemma function_sum {A B C : eqType} {alpha : Rel A C} {beta : Rel B C}:
 function_r alpha -> function_r beta -> function_r (Rel_sum alpha beta).
Proof.
elim => H H0.
elim => H1 H2.
split.
apply (total_sum H H1).
apply (univalent_sum H0 H2).
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_conjugate]
Let $\alpha :A \rel C$, $\beta :B \rel C$ and $\gamma :A+B \rel C$ be relations, $j:A \to A+B$ and $k:B \to A+B$ be inclusions. Then,
$$
j \cdot \gamma = \alpha \land k \cdot \gamma = \beta \Leftrightarrow \gamma = \alpha \bot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_conjugate
 {A B C : eqType} {alpha : Rel A C} {beta : Rel B C} {gamma : Rel (sum_eqType A B) C}:
 inl_r A B ・ gamma = alpha /\ inr_r A B ・ gamma = beta <->
 gamma = Rel_sum alpha beta.
Proof.
split; move => H.
elim H => H0 H1.
rewrite -(@comp_id_l _ _ gamma).
rewrite -inl_inr_cup_id comp_cup_distr_r comp_assoc comp_assoc.
by [rewrite H0 H1].
split.
rewrite H comp_cup_distr_l -comp_assoc -comp_assoc.
rewrite inl_id inl_inr_empty comp_id_l comp_empty_l.
by [rewrite cup_empty].
rewrite H comp_cup_distr_l -comp_assoc -comp_assoc.
rewrite inr_id inr_inl_empty comp_id_l comp_empty_l.
by [rewrite cup_comm cup_empty].
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_comp]
In below figure,
$$
(\alpha \bot \beta)^\sharp \cdot (\gamma \bot \delta) = \alpha^\sharp \cdot \gamma \sqcup \beta^\sharp \cdot \delta.
$$
$$
\xymatrix{
& & Y \ar@{-_>}[lld]_\alpha \ar@{->}[d]^j \ar@{-_>}[rrd]^\gamma & & \\
X & & Y+Z \ar@{-_>}[ll]^{\alpha \bot \beta} \ar@{-_>}[rr]_{\gamma \bot \delta} & & W \\
& & Z \ar@{-_>}[llu]^\beta \ar@{->}[u]_k \ar@{-_>}[rru]_\delta & & \\
}
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_comp {W X Y Z : eqType}
 {alpha : Rel Y X} {beta : Rel Z X} {gamma : Rel Y W} {delta : Rel Z W}:
 (Rel_sum alpha beta) # ・ Rel_sum gamma delta =
 (alpha # ・ gamma) ∪ (beta # ・ delta).
Proof.
rewrite /Rel_sum.
rewrite inv_cup_distr comp_cup_distr_l comp_cup_distr_r comp_cup_distr_r.
rewrite comp_inv comp_inv inv_invol inv_invol.
apply f_equal2.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (inl_r Y Z)) inl_id comp_id_l.
by [rewrite comp_assoc -(@comp_assoc _ _ _ _ (inr_r Y Z)) inr_inl_empty comp_empty_l comp_empty_r cup_empty].
rewrite comp_assoc -(@comp_assoc _ _ _ _ (inl_r Y Z)) inl_inr_empty comp_empty_l comp_empty_r cup_comm cup_empty.
by [rewrite comp_assoc -(@comp_assoc _ _ _ _ (inr_r Y Z)) inr_id comp_id_l].
Qed.

(** %
\subsection{分配法則}
\begin{screen}
\begin{lemma}[sum\_cap\_distr\_l]
Let $\alpha :A \rel C$ and $\beta, {\beta}' :B \rel C$. Then,
$$
\alpha \bot (\beta \sqcap {\beta}') \sqsubseteq (\alpha \bot \beta) \sqcap (\alpha \bot {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_cap_distr_l
 {A B C : eqType} {alpha : Rel A C} {beta beta' : Rel B C}:
 Rel_sum alpha (beta ∩ beta') ⊆ (Rel_sum alpha beta ∩ Rel_sum alpha beta').
Proof.
rewrite -cup_cap_distr_l.
apply cup_inc_compat_l.
apply comp_cap_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_cap\_distr\_r]
Let $\alpha, {\alpha}' :A \rel C$ and $\beta :B \rel C$. Then,
$$
(\alpha \sqcap {\alpha}') \bot \beta \sqsubseteq (\alpha \bot \beta) \sqcap ({\alpha}' \bot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_cap_distr_r
 {A B C : eqType} {alpha alpha' : Rel A C} {beta : Rel B C}:
 Rel_sum (alpha ∩ alpha') beta ⊆ (Rel_sum alpha beta ∩ Rel_sum alpha' beta).
Proof.
rewrite -cup_cap_distr_r.
apply cup_inc_compat_r.
apply comp_cap_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_cup\_distr\_l]
Let $\alpha :A \rel C$ and $\beta, {\beta}' :B \rel C$. Then,
$$
\alpha \bot (\beta \sqcup {\beta}') = (\alpha \bot \beta) \sqcup (\alpha \bot {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_cup_distr_l
 {A B C : eqType} {alpha : Rel A C} {beta beta' : Rel B C}:
 Rel_sum alpha (beta ∪ beta') = Rel_sum alpha beta ∪ Rel_sum alpha beta'.
Proof.
rewrite -cup_assoc (@cup_comm _ _ (Rel_sum alpha beta)) -cup_assoc.
by [rewrite cup_idem cup_assoc -comp_cup_distr_l].
Qed.

(** %
\begin{screen}
\begin{lemma}[sum\_cup\_distr\_r]
Let $\alpha, {\alpha}' :A \rel C$ and $\beta :B \rel C$. Then,
$$
(\alpha \sqcup {\alpha}') \bot \beta = (\alpha \bot \beta) \sqcup ({\alpha}' \bot \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma sum_cup_distr_r
 {A B C : eqType} {alpha alpha' : Rel A C} {beta : Rel B C}:
 Rel_sum (alpha ∪ alpha') beta = (Rel_sum alpha beta ∪ Rel_sum alpha' beta).
Proof.
rewrite cup_assoc (@cup_comm _ _ (inr_r A B # ・ beta)) cup_assoc.
by [rewrite cup_idem -cup_assoc -comp_cup_distr_l].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_sum\_distr\_r]
Let $\alpha :A \rel C$, $\beta :B \rel C$ and $\gamma :C \rel D$. Then,
$$
(\alpha \bot \beta) \cdot \gamma = \alpha \cdot \gamma \bot \beta \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_sum_distr_r
 {A B C D : eqType} {alpha : Rel A C} {beta : Rel B C} {gamma : Rel C D}:
 (Rel_sum alpha beta) ・ gamma = Rel_sum (alpha ・ gamma) (beta ・ gamma).
Proof.
by [rewrite comp_cup_distr_r comp_assoc comp_assoc].
Qed.

(** %
\section{関係の直積}
\subsection{射影対, 関係直積の定義}
\begin{screen}
射影対の存在公理(Axiom 24)で射影対が存在することまでは仮定済みなので, 実際に射影対 $p:A \times B \rel A,k:A \times B \rel B$ を定義する関数を定義する.
\end{screen}
% **)
Definition prod_r (A B : eqType):
 {x : (Rel (prod_eqType A B) A) * (Rel (prod_eqType A B) B) |
 (fst x) # ・ (snd x) = ∇ A B /\
 ((fst x) ・ (fst x) #) ∩ ((snd x) ・ (snd x) #) = Id (prod_eqType A B) /\
 univalent_r (fst x) /\ univalent_r (snd x)}.
apply constructive_indefinite_description.
elim (@pair_of_projections A B) => p.
elim => q H.
exists (p,q).
simpl.
apply H.
Defined.
Definition fst_r (A B : eqType):= fst (sval (prod_r A B)).
Definition snd_r (A B : eqType):= snd (sval (prod_r A B)).

(** %
\begin{screen}
またこの定義による射影対が, 射影対としての性質(Axiom 24) $+ \alpha$ を満たしていることも事前に証明しておく.
\end{screen}
% **)
Lemma fst_snd_universal {A B : eqType}: fst_r A B # ・ snd_r A B = ∇ A B.
Proof.
apply (proj2_sig (prod_r A B)).
Qed.
Lemma snd_fst_universal {A B : eqType}: snd_r A B # ・ fst_r A B = ∇ B A.
Proof.
apply inv_invol2.
rewrite comp_inv inv_invol inv_universal.
apply fst_snd_universal.
Qed.
Lemma fst_snd_cap_id {A B : eqType}:
 (fst_r A B ・ fst_r A B #) ∩ (snd_r A B ・ snd_r A B #) = Id (prod_eqType A B).
Proof.
apply (proj2_sig (prod_r A B)).
Qed.
Lemma fst_function {A B : eqType}: function_r (fst_r A B).
Proof.
move : (proj2_sig (prod_r A B)).
elim => H.
elim => H0 H1.
split.
rewrite /total_r.
rewrite -H0.
apply cap_l.
apply H1.
Qed.
Lemma snd_function {A B : eqType}: function_r (snd_r A B).
Proof.
move : (proj2_sig (prod_r A B)).
elim => H.
elim => H0 H1.
split.
rewrite /total_r.
rewrite -H0.
apply cap_r.
apply H1.
Qed.

(** %
\begin{screen}
さらに $\alpha :A \rel B$ と $\beta :A \rel C$ の関係直積 $\alpha \top \beta :A \rel B \times C$ を, $\alpha \top \beta := \alpha \cdot p^\sharp \sqcap \beta \cdot q^\sharp$ で定義する.
\end{screen}
% **)
Definition Rel_prod {A B C : eqType} (alpha : Rel A B) (beta : Rel A C):=
 (alpha ・ fst_r B C #) ∩ (beta ・ snd_r B C #).

(** %
\subsection{関係直積の性質}
\begin{screen}
\begin{lemma}[prod\_inc\_compat]
Let $\alpha, {\alpha}' :A \rel B$ and $\beta, {\beta}' :A \rel C$. Then,
$$
\alpha \sqsubseteq {\alpha}' \land \beta \sqsubseteq {\beta}' \Rightarrow \alpha \top \beta \sqsubseteq {\alpha}' \top {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_inc_compat
 {A B C : eqType} {alpha alpha' : Rel A B} {beta beta' : Rel A C}:
 alpha ⊆ alpha' -> beta ⊆ beta' -> Rel_prod alpha beta ⊆ Rel_prod alpha' beta'.
Proof.
move => H H0.
apply cap_inc_compat.
apply (comp_inc_compat_ab_a'b H).
apply (comp_inc_compat_ab_a'b H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_inc\_compat\_l]
Let $\alpha :A \rel B$ and $\beta, {\beta}' :A \rel C$. Then,
$$
\beta \sqsubseteq {\beta}' \Rightarrow \alpha \top \beta \sqsubseteq \alpha \top {\beta}'.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_inc_compat_l
 {A B C : eqType} {alpha : Rel A B} {beta beta' : Rel A C}:
 beta ⊆ beta' -> Rel_prod alpha beta ⊆ Rel_prod alpha beta'.
Proof.
move => H.
apply (prod_inc_compat (@inc_refl _ _ alpha) H).
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_inc\_compat\_r]
Let $\alpha, {\alpha}' :A \rel B$ and $\beta :A \rel C$. Then,
$$
\alpha \sqsubseteq {\alpha}' \Rightarrow \alpha \top \beta \sqsubseteq {\alpha}' \top \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_inc_compat_r
 {A B C : eqType} {alpha alpha' : Rel A B} {beta : Rel A C}:
 alpha ⊆ alpha' -> Rel_prod alpha beta ⊆ Rel_prod alpha' beta.
Proof.
move => H.
apply (prod_inc_compat H (@inc_refl _ _ beta)).
Qed.

(** %
\begin{screen}
\begin{lemma}[total\_prod]
Let $\alpha :A \rel B$ and $\beta :A \rel C$ are total relations, then $\alpha \top \beta$ is also a total relation.
\end{lemma}
\end{screen}
% **)
Lemma total_prod {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 total_r alpha -> total_r beta -> total_r (Rel_prod alpha beta).
Proof.
move => H H0.
rewrite domain_total cap_domain cap_comm.
apply Logic.eq_sym.
apply inc_def1.
apply (@inc_trans _ _ _ _ _ H).
rewrite comp_inv inv_invol comp_assoc.
apply comp_inc_compat_ab_ab'.
apply (@inc_trans _ _ _ (alpha # ・ (beta ・ beta #))).
apply (comp_inc_compat_a_ab H0).
rewrite -comp_assoc -comp_assoc fst_snd_universal.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[univalent\_prod]
Let $\alpha :A \rel B$ and $\beta :A \rel C$ are univalent relations, then $\alpha \top \beta$ is also a univalent relation.
\end{lemma}
\end{screen}
% **)
Lemma univalent_prod {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 univalent_r alpha -> univalent_r beta -> univalent_r (Rel_prod alpha beta).
Proof.
move => H H0.
rewrite /univalent_r/Rel_prod.
rewrite inv_cap_distr comp_inv inv_invol comp_inv inv_invol.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
rewrite -fst_snd_cap_id.
apply cap_inc_compat.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite comp_assoc -(@comp_assoc _ _ _ _ _ alpha).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H).
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_r)).
rewrite comp_assoc -(@comp_assoc _ _ _ _ _ beta).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_prod]
Let $\alpha :A \to B$ and $\beta :A \to C$ are functions, then $\alpha \top \beta$ is also a function.
\end{lemma}
\end{screen}
% **)
Lemma function_prod {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 function_r alpha -> function_r beta -> function_r (Rel_prod alpha beta).
Proof.
elim => H H0.
elim => H1 H2.
split.
apply (total_prod H H1).
apply (univalent_prod H0 H2).
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_fst\_surjection]
Let $p :B \times C \to B$ be a projection. Then,
$$
\mbox{``$p$ is a surjection''} \Leftrightarrow \forall D, \nabla_{BD} = \nabla_{BC} \cdot \nabla_{CD}.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_fst_surjection {B C : eqType}:
 surjection_r (fst_r B C) <-> forall D : eqType, ∇ B D = ∇ B C ・ ∇ C D.
Proof.
split; move => H.
move => D.
elim H => H0 H1.
apply inc_antisym.
apply (@inc_trans _ _ _ ((fst_r B C # ・ (fst_r B C #) #) ・ ∇ B D)).
apply (comp_inc_compat_b_ab H1).
rewrite inv_invol.
apply (@inc_trans _ _ _ (((fst_r B C # ・ snd_r B C) ・ (snd_r B C # ・ fst_r B C)) ・ ∇ B D)).
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (snd_r B C)).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_b_ab.
apply snd_function.
rewrite (@comp_assoc _ _ _ _ _ _ (∇ B D)).
apply comp_inc_compat.
apply inc_alpha_universal.
apply inc_alpha_universal.
apply inc_alpha_universal.
split.
apply fst_function.
rewrite /total_r.
rewrite -(@cap_universal _ _ (Id B)) (H B) -(@fst_snd_universal B C) cap_comm comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
rewrite comp_id_r.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_snd\_surjection]
Let $q :B \times C \to C$ be a projection. Then,
$$
\mbox{``$q$ is a surjection''} \Leftrightarrow \forall D, \nabla_{CD} = \nabla_{CB} \cdot \nabla_{BD}.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_snd_surjection {B C : eqType}:
 surjection_r (snd_r B C) <-> forall D : eqType, ∇ C D = ∇ C B ・ ∇ B D.
Proof.
split; move => H.
move => D.
elim H => H0 H1.
apply inc_antisym.
apply (@inc_trans _ _ _ ((snd_r B C # ・ (snd_r B C #) #) ・ ∇ C D)).
apply (comp_inc_compat_b_ab H1).
rewrite inv_invol.
apply (@inc_trans _ _ _ (((snd_r B C # ・ fst_r B C) ・ (fst_r B C # ・ snd_r B C)) ・ ∇ C D)).
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (fst_r B C)).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_b_ab.
apply fst_function.
rewrite (@comp_assoc _ _ _ _ _ _ (∇ C D)).
apply comp_inc_compat.
apply inc_alpha_universal.
apply inc_alpha_universal.
apply inc_alpha_universal.
split.
apply snd_function.
rewrite /total_r.
rewrite -(@cap_universal _ _ (Id C)) (H C) -(@snd_fst_universal B C) cap_comm comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
rewrite comp_id_r.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_fst\_domain1]
Let $p :B \times C \to B$ be a projection, $\alpha :A \rel B$ and $\beta :A \rel C$. Then,
$$
(\alpha \top \beta) \cdot p = \domain{\beta} \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_fst_domain1 {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 (Rel_prod alpha beta) ・ fst_r B C = domain beta ・ alpha.
Proof.
rewrite (@comp_inv_inv A A) domain_inv.
rewrite domain_universal2 inv_cap_distr comp_inv inv_invol inv_invol inv_universal.
rewrite -snd_fst_universal.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
rewrite comp_assoc comp_assoc.
apply cap_inc_compat_r.
apply comp_inc_compat_ab_a.
apply fst_function.
rewrite cap_comm -comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
rewrite cap_comm.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_fst\_domain2]
Let $p :B \times C \to B$ be a projection, $\alpha :A \rel B$ and $\beta :A \rel C$. Then,
$$
(\alpha \top \beta) \cdot p = \alpha \Leftrightarrow \domain{\alpha} \sqsubseteq \domain{\beta}.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_fst_domain2 {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 (Rel_prod alpha beta) ・ fst_r B C = alpha <-> domain alpha ⊆ domain beta.
Proof.
rewrite prod_fst_domain1.
split; move => H.
apply domain_lemma2b.
assert ((domain beta ・ alpha) ⊆ ((beta ・ beta #) ・ alpha)).
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite H in H0.
apply H0.
apply inc_antisym.
apply comp_inc_compat_ab_b.
apply cap_r.
apply (@inc_trans _ _ _ (domain alpha ・ alpha)).
rewrite domain_comp_alpha1.
apply inc_refl.
apply (comp_inc_compat_ab_a'b H).
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_snd\_domain1]
Let $q :B \times C \to C$ be a projection, $\alpha :A \rel B$ and $\beta :A \rel C$. Then,
$$
(\alpha \top \beta) \cdot q = \domain{\alpha} \cdot \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_snd_domain1 {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 (Rel_prod alpha beta) ・ snd_r B C = domain alpha ・ beta.
Proof.
rewrite (@comp_inv_inv A A) domain_inv.
rewrite domain_universal2 inv_cap_distr comp_inv inv_invol inv_invol inv_universal.
rewrite -fst_snd_universal.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
rewrite comp_assoc comp_assoc cap_comm.
apply cap_inc_compat_r.
apply comp_inc_compat_ab_a.
apply snd_function.
rewrite cap_comm -comp_assoc.
apply dedekind2.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_snd\_domain2]
Let $q :B \times C \to C$ be a projection, $\alpha :A \rel B$ and $\beta :A \rel C$. Then,
$$
(\alpha \top \beta) \cdot q = \beta \Leftrightarrow \domain{\beta} \sqsubseteq \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_snd_domain2 {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 (Rel_prod alpha beta) ・ snd_r B C = beta <-> domain beta ⊆ domain alpha.
Proof.
rewrite prod_snd_domain1.
split; move => H.
apply domain_lemma2b.
assert ((domain alpha ・ beta) ⊆ ((alpha ・ alpha #) ・ beta)).
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite H in H0.
apply H0.
apply inc_antisym.
apply comp_inc_compat_ab_b.
apply cap_r.
apply (@inc_trans _ _ _ (domain beta ・ beta)).
rewrite domain_comp_alpha1.
apply inc_refl.
apply (comp_inc_compat_ab_a'b H).
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_to\_cap]
Let $\alpha :A \rel B$ and $\beta :A \rel C$. Then,
$$
\domain{\alpha \top \beta} = \domain{\alpha} \sqcap \domain{\beta}.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_to_cap {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 domain (Rel_prod alpha beta) = domain alpha ∩ domain beta.
Proof.
replace (domain (Rel_prod alpha beta)) with (domain (Rel_prod alpha beta ・ snd_r B C)).
rewrite prod_snd_domain1 comp_domain8.
apply dedekind_id3.
apply cap_r.
apply cap_r.
apply cap_r.
apply comp_domain3.
apply snd_function.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_conjugate1]
Let $\alpha :A \to B$ and $\beta :A \to C$ be functions, $p:B \times C \to B$ and $q:B \times C \to C$ be projections. Then,
$$
(\alpha \top \beta) \cdot p = \alpha \land (\alpha \top \beta) \cdot q = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_conjugate1 {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 function_r alpha -> function_r beta ->
 Rel_prod alpha beta ・ fst_r B C = alpha /\ Rel_prod alpha beta ・ snd_r B C = beta.
Proof.
move => H H0.
split.
rewrite prod_fst_domain1.
elim H0 => H1 H2.
apply inc_def1 in H1.
rewrite /domain.
by [rewrite cap_comm -H1 comp_id_l].
rewrite prod_snd_domain1.
elim H => H1 H2.
apply inc_def1 in H1.
rewrite /domain.
by [rewrite cap_comm -H1 comp_id_l].
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_conjugate2]
Let $\gamma :A \to B \times C$ be a function, $p:B \times C \to B$ and $q:B \times C \to C$ be projections. Then,
$$
(\gamma \cdot p) \top (\gamma \cdot q) = \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_conjugate2 {A B C : eqType} {gamma : Rel A (prod_eqType B C)}:
 function_r gamma -> Rel_prod (gamma ・ fst_r B C) (gamma ・ snd_r B C) = gamma.
Proof.
move => H.
rewrite /Rel_prod.
rewrite comp_assoc comp_assoc -(function_cap_distr_l H).
by [rewrite fst_snd_cap_id comp_id_r].
Qed.

(** %
\begin{screen}
\begin{lemma}[diagonal\_conjugate]
Let $p:B \times C \to B$ and $q:B \times C \to C$ be projections. Then,
$$
\frac{\alpha :A \rel B}{u \sqsubseteq id_{A \times B}} \,\, \frac{\alpha = p^\sharp \cdot u \cdot q}{u = \domain{p \cdot \alpha \sqcap q}}.
$$
\end{lemma}
\end{screen}
% **)
Lemma diagonal_conjugate {A B : eqType} {alpha : Rel A B}:
 conjugate A B (prod_eqType A B) (prod_eqType A B)
 True_r (fun u => u ⊆ Id (prod_eqType A B))
 (fun u => (fst_r A B # ・ u) ・ snd_r A B)
 (fun alpha => domain ((fst_r A B ・ alpha) ∩ snd_r A B)).
Proof.
split.
move => alpha0 H.
split.
apply cap_r.
rewrite cap_domain.
apply inc_antisym.
apply (@inc_trans _ _ _ ((fst_r A B # ・ ((fst_r A B ・ alpha0) ・ snd_r A B #)) ・ snd_r A B)).
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
apply cap_l.
rewrite comp_assoc comp_assoc -comp_assoc -(@comp_assoc _ _ _ _ (fst_r A B #)).
apply (@inc_trans _ _ _ ((fst_r A B # ・ fst_r A B) ・ alpha0)).
apply comp_inc_compat_ab_a.
apply snd_function.
apply comp_inc_compat_ab_b.
apply fst_function.
apply (@inc_trans _ _ _ (alpha0 ∩ ((fst_r A B # ・ Id (prod_eqType A B)) ・ snd_r A B))).
rewrite comp_id_r fst_snd_universal cap_universal.
apply inc_refl.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply comp_inc_compat_ab_a'b.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
rewrite cap_comm inv_invol comp_assoc.
apply inc_refl.
move => u H.
split.
by [].
replace ((fst_r A B ・ ((fst_r A B # ・ u) ・ snd_r A B)) ∩ snd_r A B) with (u ・ snd_r A B).
apply domain_inc_id in H.
move : (@snd_function A B) => H0.
elim H0 => H1 H2.
by [rewrite (comp_domain3 H1) H].
rewrite comp_assoc -comp_assoc.
apply inc_antisym.
apply (@inc_trans _ _ _ ((u ・ snd_r A B) ∩ snd_r A B)).
apply inc_cap.
split.
apply inc_refl.
apply (comp_inc_compat_ab_b H).
apply cap_inc_compat_r.
apply comp_inc_compat_b_ab.
apply fst_function.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply comp_inc_compat_ab_b.
rewrite -fst_snd_cap_id.
apply cap_inc_compat_l.
apply comp_inc_compat_ab_ab'.
apply inc_inv.
apply (comp_inc_compat_ab_b H).
Qed.

(** %
\subsection{鋭敏性}
\begin{screen}
この節の補題は以下の 1 つのみだが, 証明が異様に長いため単独の節を設ける.
\begin{lemma}[sharpness]
In below figure,
$$
\alpha \cdot \gamma^\sharp \sqcap \beta \cdot \delta^\sharp = (\alpha \cdot p^\sharp \sqcap \beta \cdot q^\sharp) \cdot (p \cdot \gamma^\sharp \sqcap q \cdot \delta^\sharp).
$$
$$
\xymatrix{
& Y & \\
X \ar@{-_>}[ru]^\alpha \ar@{-_>}[rd]_\beta & Y \times Z \ar@{->}[u]^p \ar@{->}[d]_q & W \ar@{-_>}[lu]_\gamma \ar@{-_>}[ld]^\delta \\
& Z & \\
}
$$
\end{lemma}
\end{screen}
% **)
Lemma sharpness {W X Y Z : eqType}
 {alpha : Rel X Y} {beta : Rel X Z} {gamma : Rel W Y} {delta : Rel W Z}:
 (alpha ・ gamma #) ∩ (beta ・ delta #) =
 ((alpha ・ fst_r Y Z #) ∩ (beta ・ snd_r Y Z #))
 ・ ((fst_r Y Z ・ gamma #) ∩ (snd_r Y Z ・ delta #)).
Proof.
apply inc_antisym.
move : (rationality _ _ alpha) => H.
move : (rationality _ _ beta) => H0.
move : (rationality _ _ (gamma #)) => H1.
move : (rationality _ _ (delta #)) => H2.
elim H => R.
elim => f0.
elim => g0 H3.
elim H0 => R0.
elim => f1.
elim => g1 H4.
elim H1 => R1.
elim => h0.
elim => k0 H5.
elim H2 => R2.
elim => h1.
elim => k1 H6.
move : (rationality _ _ (g0 ・ h0 #)) => H7.
move : (rationality _ _ (g1 ・ h1 #)) => H8.
move : (rationality _ _ ((alpha ・ gamma #) ∩ (beta ・ delta #))) => H9.
elim H7 => R3.
elim => s0.
elim => t0 H10.
elim H8 => R4.
elim => s1.
elim => t1 H11.
elim H9 => R5.
elim => x.
elim => z H12.
assert (alpha ・ gamma # = (f0 # ・ (s0 # ・ t0)) ・ k0).
replace alpha with (f0 # ・ g0).
replace (gamma #) with (h0 # ・ k0).
rewrite -comp_assoc (@comp_assoc _ _ _ _ (f0 #)).
apply f_equal2.
apply f_equal.
apply H10.
by [].
apply Logic.eq_sym.
apply H5.
apply Logic.eq_sym.
apply H3.
assert (beta ・ delta # = (f1 # ・ (s1 # ・ t1)) ・ k1).
replace beta with (f1 # ・ g1).
replace (delta #) with (h1 # ・ k1).
rewrite -comp_assoc (@comp_assoc _ _ _ _ (f1 #)).
apply f_equal2.
apply f_equal.
apply H11.
by [].
apply Logic.eq_sym.
apply H6.
apply Logic.eq_sym.
apply H4.
assert (t0 ・ h0 = s0 ・ g0).
apply function_inc.
apply function_comp.
apply H10.
apply H5.
apply function_comp.
apply H10.
apply H3.
apply (@inc_trans _ _ _ (s0 ・ ((s0 # ・ t0) ・ h0))).
rewrite comp_assoc -comp_assoc.
apply comp_inc_compat_b_ab.
apply H10.
apply comp_inc_compat_ab_ab'.
replace (s0 # ・ t0) with (g0 ・ h0 #).
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H5.
apply H10.
assert (t1 ・ h1 = s1 ・ g1).
apply function_inc.
apply function_comp.
apply H11.
apply H6.
apply function_comp.
apply H11.
apply H4.
apply (@inc_trans _ _ _ (s1 ・ ((s1 # ・ t1) ・ h1))).
rewrite comp_assoc -comp_assoc.
apply comp_inc_compat_b_ab.
apply H11.
apply comp_inc_compat_ab_ab'.
replace (s1 # ・ t1) with (g1 ・ h1 #).
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H6.
apply H11.
remember ((x ・ (s0 ・ f0) #) ∩ (z ・ (t0 ・ k0) #)) as m0.
remember ((x ・ (s1 ・ f1) #) ∩ (z ・ (t1 ・ k1) #)) as m1.
assert (total_r m0).
rewrite Heqm0.
apply domain_corollary1.
apply H12.
apply H12.
replace (x # ・ z) with ((alpha ・ gamma #) ∩ (beta ・ delta #)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite comp_inv H13 -comp_assoc comp_assoc.
apply inc_refl.
apply H12.
assert (total_r m1).
rewrite Heqm1.
apply domain_corollary1.
apply H12.
apply H12.
replace (x # ・ z) with ((alpha ・ gamma #) ∩ (beta ・ delta #)).
apply (@inc_trans _ _ _ _ _ (cap_r)).
rewrite comp_inv H14 -comp_assoc comp_assoc.
apply inc_refl.
apply H12.
remember (m0 ・ (s0 ・ g0)) as n0.
remember (m1 ・ (s1 ・ g1)) as n1.
assert (total_r n0).
rewrite Heqn0.
apply (total_comp H17).
apply total_comp.
apply H10.
apply H3.
assert (total_r n1).
rewrite Heqn1.
apply (total_comp H18).
apply total_comp.
apply H11.
apply H4.
assert (total_r ((n0 ・ fst_r Y Z #) ∩ (n1 ・ snd_r Y Z #))).
apply (domain_corollary1 H19 H20).
rewrite fst_snd_universal.
apply inc_alpha_universal.
assert ((x # ・ n0) ⊆ alpha).
replace alpha with (f0 # ・ g0).
rewrite Heqn0 Heqm0.
apply (@inc_trans _ _ _ (((x # ・ x) ・ f0 #) ・ ((s0 # ・ s0) ・ g0))).
rewrite comp_assoc comp_assoc.
apply comp_inc_compat_ab_ab'.
rewrite -comp_assoc -comp_assoc -comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc -comp_inv.
apply cap_l.
apply comp_inc_compat.
apply comp_inc_compat_ab_b.
apply H12.
apply comp_inc_compat_ab_b.
apply H10.
apply Logic.eq_sym.
apply H3.
assert ((x # ・ n1) ⊆ beta).
replace beta with (f1 # ・ g1).
rewrite Heqn1 Heqm1.
apply (@inc_trans _ _ _ (((x # ・ x) ・ f1 #) ・ ((s1 # ・ s1) ・ g1))).
rewrite comp_assoc comp_assoc.
apply comp_inc_compat_ab_ab'.
rewrite -comp_assoc -comp_assoc -comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc -comp_inv.
apply cap_l.
apply comp_inc_compat.
apply comp_inc_compat_ab_b.
apply H12.
apply comp_inc_compat_ab_b.
apply H11.
apply Logic.eq_sym.
apply H4.
assert ((n0 # ・ z) ⊆ gamma #).
replace (gamma #) with (h0 # ・ k0).
rewrite Heqn0 Heqm0 -H15 comp_inv comp_inv inv_cap_distr.
apply (@inc_trans _ _ _ ((h0 # ・ (t0 # ・ t0)) ・ (k0 ・ (z # ・ z)))).
rewrite -comp_assoc -comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc comp_assoc comp_assoc comp_assoc.
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_ab'.
rewrite -comp_assoc (@comp_inv _ _ _ z) inv_invol.
apply cap_r.
apply comp_inc_compat.
apply comp_inc_compat_ab_a.
apply H10.
apply comp_inc_compat_ab_a.
apply H12.
apply Logic.eq_sym.
apply H5.
assert ((n1 # ・ z) ⊆ delta #).
replace (delta #) with (h1 # ・ k1).
rewrite Heqn1 Heqm1 -H16 comp_inv comp_inv inv_cap_distr.
apply (@inc_trans _ _ _ ((h1 # ・ (t1 # ・ t1)) ・ (k1 ・ (z # ・ z)))).
rewrite -comp_assoc -comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc comp_assoc comp_assoc comp_assoc.
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_ab'.
rewrite -comp_assoc (@comp_inv _ _ _ z) inv_invol.
apply cap_r.
apply comp_inc_compat.
apply comp_inc_compat_ab_a.
apply H11.
apply comp_inc_compat_ab_a.
apply H12.
apply Logic.eq_sym.
apply H6.
replace ((alpha ・ gamma #) ∩ (beta ・ delta #)) with (x # ・ z).
apply (@inc_trans _ _ _ ((x # ・ (((n0 ・ fst_r Y Z #) ∩ (n1 ・ snd_r Y Z #)) ・ (((n0 ・ fst_r Y Z #) ∩ (n1 ・ snd_r Y Z #))) #)) ・ z)).
apply comp_inc_compat_ab_a'b.
apply (comp_inc_compat_a_ab H21).
rewrite -comp_assoc comp_assoc.
apply comp_inc_compat.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply cap_inc_compat.
rewrite -comp_assoc.
apply (comp_inc_compat_ab_a'b H22).
rewrite -comp_assoc.
apply (comp_inc_compat_ab_a'b H23).
rewrite inv_cap_distr comp_inv comp_inv inv_invol inv_invol.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply cap_inc_compat.
rewrite comp_assoc.
apply (comp_inc_compat_ab_ab' H24).
rewrite comp_assoc.
apply (comp_inc_compat_ab_ab' H25).
apply Logic.eq_sym.
apply H12.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply cap_inc_compat.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite -comp_assoc (@comp_assoc _ _ _ _ alpha).
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_a.
apply fst_function.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_r)).
rewrite -comp_assoc (@comp_assoc _ _ _ _ beta).
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_a.
apply snd_function.
Qed.

(** %
\subsection{分配法則}
\begin{screen}
\begin{lemma}[prod\_cap\_distr\_l]
Let $\alpha :A \rel B$ and $\beta, {\beta}' :A \rel C$. Then,
$$
\alpha \top (\beta \sqcap {\beta}') = (\alpha \top \beta) \sqcap (\alpha \top {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_cap_distr_l {A B C : eqType} {alpha : Rel A B} {beta beta' : Rel A C}:
 Rel_prod alpha (beta ∩ beta') = Rel_prod alpha beta ∩ Rel_prod alpha beta'.
Proof.
rewrite /Rel_prod.
rewrite -cap_assoc (@cap_comm _ _ _ (alpha ・ fst_r B C #)) -cap_assoc cap_idem cap_assoc.
apply f_equal.
apply function_cap_distr_r.
apply snd_function.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_cap\_distr\_r]
Let $\alpha, {\alpha}' :A \rel B$ and $\beta :A \rel C$. Then,
$$
(\alpha \sqcap {\alpha}') \top \beta = (\alpha \top \beta) \sqcap ({\alpha}' \top \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_cap_distr_r {A B C : eqType} {alpha alpha' : Rel A B} {beta : Rel A C}:
 Rel_prod (alpha ∩ alpha') beta = Rel_prod alpha beta ∩ Rel_prod alpha' beta.
Proof.
rewrite /Rel_prod.
rewrite cap_assoc (@cap_comm _ _ (beta ・ snd_r B C #)) cap_assoc cap_idem -cap_assoc.
apply (@f_equal _ _ (fun x => @cap _ _ x (beta ・ snd_r B C #))).
apply function_cap_distr_r.
apply fst_function.
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_cup\_distr\_l]
Let $\alpha :A \rel B$ and $\beta, {\beta}' :A \rel C$. Then,
$$
\alpha \top (\beta \sqcup {\beta}') = (\alpha \top \beta) \sqcup (\alpha \top {\beta}').
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_cup_distr_l {A B C : eqType} {alpha : Rel A B} {beta beta' : Rel A C}:
 Rel_prod alpha (beta ∪ beta') = Rel_prod alpha beta ∪ Rel_prod alpha beta'.
Proof.
by [rewrite -cap_cup_distr_l -comp_cup_distr_r].
Qed.

(** %
\begin{screen}
\begin{lemma}[prod\_cup\_distr\_r]
Let $\alpha, {\alpha}' :A \rel B$ and $\beta :A \rel C$. Then,
$$
(\alpha \sqcup {\alpha}') \top \beta = (\alpha \top \beta) \sqcup ({\alpha}' \top \beta).
$$
\end{lemma}
\end{screen}
% **)
Lemma prod_cup_distr_r {A B C : eqType} {alpha alpha' : Rel A B} {beta : Rel A C}:
 Rel_prod (alpha ∪ alpha') beta = Rel_prod alpha beta ∪ Rel_prod alpha' beta.
Proof.
by [rewrite -cap_cup_distr_r -comp_cup_distr_r].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_prod\_distr\_l]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\gamma :B \rel D$. Then,
$$
\alpha \cdot (\beta \top \gamma) \sqsubseteq \alpha \cdot \beta \top \alpha \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_prod_distr_l
 {A B C D : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel B D}:
 alpha ・ Rel_prod beta gamma ⊆ Rel_prod (alpha ・ beta) (alpha ・ gamma).
Proof.
rewrite /Rel_prod.
rewrite comp_assoc comp_assoc.
apply comp_cap_distr_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_prod\_distr\_l]
Let $\alpha :A \rel B$ be a function, $\beta :B \rel C$ and $\gamma :B \rel D$. Then,
$$
\alpha \cdot (\beta \top \gamma) = \alpha \cdot \beta \top \alpha \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_prod_distr_l
 {A B C D : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel B D}:
 function_r alpha -> alpha ・ Rel_prod beta gamma = Rel_prod (alpha ・ beta) (alpha ・ gamma).
Proof.
move => H.
rewrite /Rel_prod.
rewrite comp_assoc comp_assoc.
apply (function_cap_distr_l H).
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_prod\_universal]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\gamma :D \rel E$. Then,
$$
\alpha \cdot (\beta \top \nabla_{BD} \cdot \gamma) = \alpha \cdot \beta \top \nabla_{AD} \cdot \gamma.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_prod_universal
 {A B C D E : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel D E}:
 alpha ・ Rel_prod beta (∇ B D ・ gamma) = Rel_prod (alpha ・ beta) (∇ A D ・ gamma).
Proof.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (comp_prod_distr_l)).
apply prod_inc_compat_l.
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
rewrite /Rel_prod.
rewrite comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
apply cap_inc_compat_l.
rewrite comp_assoc comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[fst\_cap\_snd\_distr]
Let $u,v :A \times B \rel A \times B$ and $u,v \sqsubseteq id_{A \times B}$, $p:B \times C \to B$ and $q:B \times C \to C$ be projections. Then,
$$
p^\sharp \cdot (u \sqcap v) \cdot q = p^\sharp \cdot u \cdot q \sqcap p^\sharp \cdot v \cdot q.
$$
\end{lemma}
\end{screen}
% **)
Lemma fst_cap_snd_distr
 {A B : eqType} {u v : Rel (prod_eqType A B) (prod_eqType A B)}:
 u ⊆ Id (prod_eqType A B) -> v ⊆ Id (prod_eqType A B) ->
 fst_r A B # ・ (u ∩ v) ・ snd_r A B =
 ((fst_r A B # ・ u) ・ snd_r A B) ∩ ((fst_r A B # ・ v) ・ snd_r A B).
Proof.
move => H H0.
apply inc_antisym.
apply (fun H' => @inc_trans _ _ _ _ _ H' (comp_cap_distr_r)).
apply comp_inc_compat_ab_a'b.
apply comp_cap_distr_l.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
rewrite -(dedekind_id3 H H0) -(@comp_assoc _ _ _ _ _ u) (@comp_assoc _ _ _ _ (fst_r A B # ・ u) v).
apply comp_inc_compat_ab_ab'.
rewrite cap_comm comp_assoc -comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply comp_inc_compat_ab_b.
rewrite comp_inv comp_inv inv_invol -fst_snd_cap_id.
apply cap_inc_compat.
rewrite comp_assoc (dedekind_id1 H).
apply (comp_inc_compat_ab_b H).
rewrite -comp_assoc (dedekind_id1 H0).
apply (comp_inc_compat_ab_a H0).
Qed.
