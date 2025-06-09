From MyLib Require Import Basic_Notations Basic_Lemmas Relation_Properties Functions_Mappings Dedekind.
Require Import Logic.FunctionalExtensionality.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Module Relation_Properties := Relation_Properties.main def.
Module Functions_Mappings := Functions_Mappings.main def.
Module Dedekind := Dedekind.main def.
Import Basic_Lemmas Relation_Properties Functions_Mappings Dedekind.

(** %
\section{定義域の定義}
\begin{screen}
関係 $\alpha :A \rel B$ に対して, その定義域(関係) $\domain{\alpha} :A \rel A$ は,
$$
\domain{\alpha} = \alpha \cdot \alpha^\sharp \sqcap id_A
$$
で表される. また, Coq では以下のように表すことにする.
\end{screen}
% **)
Definition domain {A B : eqType} (alpha : Rel A B):= (alpha ・ alpha #) ∩ Id A.

(** %
\section{定義域の性質}
\subsection{基本的な性質}
\begin{screen}
\begin{lemma}[domain\_another\_def]
Let $\alpha :A \rel B$. Then,
$$
\domain{\alpha} = \alpha \cdot \nabla_{BA} \sqcap id_A.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_another_def {A B : eqType} {alpha : Rel A B}:
 domain alpha = (alpha ・ ∇ B A) ∩ Id A.
Proof.
apply inc_antisym.
apply cap_inc_compat_r.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
apply inc_cap.
split.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
rewrite cap_comm comp_id_r cap_universal.
apply inc_refl.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_inv]
Let $\alpha :A \rel B$. Then,
$$
\domain{\alpha}^\sharp = \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_inv {A B : eqType} {alpha : Rel A B}:
 (domain alpha) # = domain alpha.
Proof.
apply dedekind_id1.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_comp\_alpha1, domain\_comp\_alpha2]
Let $\alpha :A \rel B$. Then,
$$
\domain{\alpha} \cdot \alpha = \alpha \land \alpha^\sharp \cdot \domain{\alpha} = \alpha^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_comp_alpha1 {A B : eqType} {alpha : Rel A B}:
 (domain alpha) ・ alpha = alpha.
Proof.
apply inc_antisym.
apply comp_inc_compat_ab_b.
apply cap_r.
rewrite /domain.
rewrite cap_comm.
apply (fun H' => @inc_trans _ _ _ _ _ H' (dedekind2)).
rewrite comp_id_l cap_idem.
apply inc_refl.
Qed.

Lemma domain_comp_alpha2 {A B : eqType} {alpha : Rel A B}:
 alpha # ・ (domain alpha) = alpha #.
Proof.
rewrite -domain_inv -comp_inv.
apply f_equal.
apply domain_comp_alpha1.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_inc\_compat]
Let $\alpha, {\alpha}' :A \rel B$. Then,
$$
\alpha \sqsubseteq {\alpha}' \Rightarrow \domain{\alpha} \sqsubseteq \domain{{\alpha}'}.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_inc_compat {A B : eqType} {alpha alpha' : Rel A B}:
 alpha ⊆ alpha' -> domain alpha ⊆ domain alpha'.
Proof.
move => H.
apply cap_inc_compat_r.
apply comp_inc_compat.
apply H.
apply (@inc_inv _ _ _ _ H).
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_total]
Let $\alpha :A \rel B$. Then,
$$
\mbox{``$\alpha$ is total''} \Leftrightarrow \domain{\alpha} = id_A.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_total {A B : eqType} {alpha : Rel A B}:
 total_r alpha <-> domain alpha = Id A.
Proof.
split; move => H.
rewrite /domain.
rewrite cap_comm.
apply Logic.eq_sym.
apply inc_def1.
apply H.
apply inc_def1.
rewrite /domain in H.
by [rewrite cap_comm H].
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_inc\_id]
Let $u :A \rel A$. Then,
$$
u \sqsubseteq id_A \Leftrightarrow \domain{u} = u.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_inc_id {A : eqType} {u : Rel A A}: u ⊆ Id A <-> domain u = u.
Proof.
split; move => H.
rewrite /domain.
rewrite (dedekind_id1 H) (dedekind_id2 H).
apply inc_def1 in H.
by [rewrite -H].
rewrite -H.
apply cap_r.
Qed.

(** %
\subsection{合成と定義域}
\begin{screen}
\begin{lemma}[comp\_domain1, comp\_domain2]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
\domain{\alpha \cdot \beta} = \domain{\alpha \cdot \domain{\beta}} \sqsubseteq \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain1 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 domain (alpha ・ beta) ⊆ domain alpha.
Proof.
rewrite /domain.
rewrite comp_inv.
apply (@inc_trans _ _ _ ((alpha ・ ((beta ・ (beta # ・ alpha #)) ∩ alpha #)) ∩ Id A)).
replace (((alpha ・ beta) ・ (beta # ・ alpha #)) ∩ Id A) with ((((alpha ・ beta) ・ (beta # ・ alpha #)) ∩ Id A) ∩ Id A).
apply cap_inc_compat_r.
rewrite comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
rewrite comp_id_r.
apply inc_refl.
by [rewrite cap_assoc cap_idem].
apply cap_inc_compat_r.
apply comp_inc_compat_ab_ab'.
apply cap_r.
Qed.

Lemma comp_domain2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 domain (alpha ・ beta) = domain (alpha ・ domain beta).
Proof.
apply inc_antisym.
replace (domain (alpha ・ beta)) with (domain ((alpha ・ domain beta) ・ beta)).
apply comp_domain1.
by [rewrite comp_assoc domain_comp_alpha1].
apply (@inc_trans _ _ _ (domain (alpha ・ (beta ・ beta #)))).
apply domain_inc_compat.
apply comp_inc_compat_ab_ab'.
apply cap_l.
rewrite -comp_assoc.
apply comp_domain1.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_domain3]
Let $\alpha :A \rel B$ be a relation and $\beta :B \rel C$ be a total relation. Then,
$$
\domain{\alpha \cdot \beta} = \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain3 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 total_r beta -> domain (alpha ・ beta) = domain alpha.
Proof.
move => H.
apply inc_antisym.
apply comp_domain1.
rewrite /domain.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ beta).
apply cap_inc_compat_r.
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H).
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_domain4]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
\domain{\alpha^\sharp} \sqsubseteq \domain{\beta} \Rightarrow \domain{\alpha \cdot \beta} = \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain4 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 domain (alpha #) ⊆ domain beta -> domain (alpha ・ beta) = domain alpha.
Proof.
move => H.
apply inc_antisym.
apply comp_domain1.
rewrite /domain.
rewrite -(@domain_comp_alpha1 _ _ (alpha #)) comp_inv comp_assoc -(@comp_assoc _ _ _ _ beta).
apply cap_inc_compat_r.
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_a'b.
apply (@inc_trans _ _ _ _ _ H).
apply cap_l.
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_domain5]
Let $\alpha :A \rel B$ be a univalent relation and $\beta :B \rel C$. Then,
$$
\domain{\alpha^\sharp} \sqsubseteq \domain{\beta} \Leftrightarrow \domain{\alpha \cdot \beta} = \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain5 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r alpha ->
 (domain (alpha #) ⊆ domain beta <-> domain (alpha ・ beta) = domain alpha).
Proof.
move => H.
split; move => H0.
apply (comp_domain4 H0).
rewrite /domain.
rewrite inv_invol.
apply cap_inc_compat_r.
replace (alpha # ・ alpha) with (alpha # ・ (domain (alpha ・ beta) ・ alpha)).
rewrite /domain.
rewrite comp_inv.
apply (@inc_trans _ _ _ (alpha # ・ (((alpha ・ beta) ・ (beta # ・ alpha #)) ・ alpha))).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite comp_assoc comp_assoc comp_assoc -comp_assoc -(@comp_assoc _ _ _ _ beta).
apply (@inc_trans _ _ _ _ _ (comp_inc_compat_ab_b H)).
apply (comp_inc_compat_ab_a H).
by [rewrite H0 domain_comp_alpha1].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_domain6]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
\alpha \cdot \domain{\beta} \sqsubseteq \domain{\alpha \cdot \beta} \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain6 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 (alpha ・ domain beta) ⊆ (domain (alpha ・ beta) ・ alpha).
Proof.
apply (@inc_trans _ _ _ _ _ (@comp_cap_distr_l _ _ _ _ _ _ )).
rewrite cap_comm.
replace (alpha ・ Id B) with (Id A ・ alpha).
apply (@inc_trans _ _ _ _ _ (dedekind2)).
rewrite cap_comm -comp_assoc comp_assoc -comp_inv.
apply inc_refl.
by [rewrite comp_id_l comp_id_r].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_domain7]
Let $\alpha :A \rel B$ be a univalent relation and $\beta :B \rel C$. Then,
$$
\alpha \cdot \domain{\beta} = \domain{\alpha \cdot \beta} \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain7 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r alpha -> alpha ・ domain beta = domain (alpha ・ beta) ・ alpha.
Proof.
move => H.
apply inc_antisym.
apply comp_domain6.
apply (@inc_trans _ _ _ _ _ (@comp_cap_distr_r _ _ _ _ _ _ )).
rewrite comp_id_l comp_inv comp_assoc comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
apply comp_inc_compat_ab_ab'.
apply (fun H' => cap_inc_compat H' H).
rewrite comp_assoc -comp_assoc.
apply (comp_inc_compat_ab_a H).
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_domain8]
Let $u:A \rel A$, $\alpha :A \rel B$ and $u \sqsubseteq id_A$. Then,
$$
\domain{u \cdot \alpha} = u \cdot \domain{\alpha}.
$$
\end{lemma}
\end{screen}
% **)
Lemma comp_domain8 {A B : eqType} {u : Rel A A} {alpha : Rel A B}:
 u ⊆ Id A -> domain (u ・ alpha) = u ・ domain alpha.
Proof.
move => H.
apply inc_antisym.
rewrite -(@cap_idem _ _ (domain (u ・ alpha))).
rewrite (dedekind_id3 H).
apply cap_inc_compat.
apply (@inc_trans _ _ _ _ _ (comp_domain1)).
apply domain_inc_id in H.
rewrite H.
apply inc_refl.
apply domain_inc_compat.
apply (comp_inc_compat_ab_b H).
apply cap_r.
apply (@inc_trans _ _ _ _ _ (comp_domain6)).
apply (comp_inc_compat_ab_a H).
Qed.

(** %
\subsection{その他の性質}
\begin{screen}
\begin{lemma}[cap\_domain]
Let $\alpha, {\alpha}' :A \rel B$. Then,
$$
\domain{\alpha \sqcap {\alpha}'} = \alpha \cdot {\alpha}'^\sharp \sqcap id_A.
$$
\end{lemma}
\end{screen}
% **)
Lemma cap_domain {A B : eqType} {alpha alpha' : Rel A B}:
 domain (alpha ∩ alpha') = (alpha ・ alpha' #) ∩ Id A.
Proof.
apply inc_antisym.
apply cap_inc_compat_r.
apply comp_inc_compat.
apply cap_l.
apply inc_inv.
apply cap_r.
rewrite -(@cap_idem _ _ (Id A)) -cap_assoc.
apply cap_inc_compat_r.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
rewrite inv_invol comp_id_l comp_id_r -inv_cap_distr (@cap_comm _ _ alpha').
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[cupP\_domain\_distr, cup\_domain\_distr]
Let $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
\domain{\sqcup_{P(\alpha)} f(\alpha)} = \sqcup_{P(\alpha)} \domain{f(\alpha)}.
$$
\end{lemma}
\end{screen}
% **)
Lemma cupP_domain_distr {A B C D : eqType} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 domain (∪_{P} f) = ∪_{P} (fun alpha : Rel C D => domain (f alpha)).
Proof.
rewrite /domain.
rewrite inv_cupP_distr comp_cupP_distr_l cap_cupP_distr_r.
apply cupP_eq.
move => alpha H.
rewrite -cap_domain -cap_domain.
apply f_equal.
rewrite cap_idem.
apply inc_antisym.
apply cap_r.
apply inc_cap.
split.
move : alpha H.
apply inc_cupP.
apply inc_refl.
apply inc_refl.
Qed.

Lemma cup_domain_distr {A B : eqType} {alpha alpha' : Rel A B}:
 domain (alpha ∪ alpha') = domain alpha ∪ domain alpha'.
Proof.
rewrite cup_to_cupP (@cup_to_cupP _ _ _ _ _ _ id).
apply cupP_domain_distr.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_universal1]
Let $\alpha :A \rel B$. Then,
$$
\domain{\alpha} \cdot \nabla_{AC} = \alpha \cdot \nabla_{BC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_universal1 {A B C : eqType} {alpha : Rel A B}:
 domain alpha ・ ∇ A C = alpha ・ ∇ B C.
Proof.
apply inc_antisym.
apply (@inc_trans _ _ _ ((alpha ・ alpha #) ・ ∇ A C)).
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ ((domain alpha ・ alpha) ・ ∇ B C)).
rewrite domain_comp_alpha1.
apply inc_refl.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_universal2]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
\alpha \cdot \domain{\beta} = \alpha \sqcap \nabla_{AC} \cdot \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_universal2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 alpha ・ domain beta = alpha ∩ (∇ A C ・ beta #).
Proof.
apply inc_antisym.
apply inc_cap.
split.
apply comp_inc_compat_ab_a.
apply cap_r.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
rewrite -inv_universal -comp_inv -domain_universal1.
rewrite comp_inv inv_universal domain_inv cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
apply comp_inc_compat_ab_a'b.
rewrite cap_comm cap_universal domain_inv.
apply comp_inc_compat_ab_a.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_lemma1]
Let $\alpha, \beta :A \rel B$ and $\beta$ is univalent. Then,
$$
\alpha \sqsubseteq \beta \land \domain{\alpha} = \domain{\beta} \Rightarrow \alpha = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_lemma1 {A B : eqType} {alpha beta : Rel A B}:
 univalent_r beta -> alpha ⊆ beta -> domain alpha = domain beta -> alpha = beta.
Proof.
move => H H0 H1.
apply inc_antisym.
apply H0.
rewrite -(@domain_comp_alpha1 _ _ beta) -H1.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
apply comp_inc_compat_ab_a'b.
apply (@inc_inv _ _ _ _ H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_lemma2a, domain\_lemma2b]
Let $\alpha :A \rel B$ and $\beta :A \rel C$. Then,
$$
\domain{\alpha} \sqsubseteq \domain{\beta} \Leftrightarrow \alpha \cdot \nabla_{BB} \sqsubseteq \beta \cdot \nabla_{CB} \Leftrightarrow \alpha \sqsubseteq \beta \cdot \beta^\sharp \cdot \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_lemma2a {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 domain alpha ⊆ domain beta <-> (alpha ・ ∇ B B) ⊆ (beta ・ ∇ C B).
Proof.
split; move => H.
rewrite -(@domain_comp_alpha1 _ _ alpha) comp_assoc.
apply (@inc_trans _ _ _ _ _ (comp_inc_compat_ab_a'b H)).
apply (@inc_trans _ _ _ _ _ (comp_inc_compat_ab_a'b (cap_l))).
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ (domain ((beta ・ beta #) ・ alpha))).
apply domain_inc_compat.
apply (@inc_trans _ _ _ (alpha ∩ (beta ・ ∇ C B))).
apply (fun H' => @inc_trans _ _ _ _ _ H' (cap_inc_compat_l H)).
replace (alpha ∩ (alpha ・ ∇ B B)) with ((alpha ・ Id B) ∩ (alpha ・ ∇ B B)).
apply (fun H' => @inc_trans _ _ _ _ _ H' (comp_cap_distr_l)).
rewrite cap_universal comp_id_r.
apply inc_refl.
by [rewrite comp_id_r].
rewrite cap_comm comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
rewrite cap_comm cap_universal.
apply inc_refl.
rewrite comp_assoc.
apply comp_domain1.
Qed.
Lemma domain_lemma2b {A B C : eqType} {alpha : Rel A B} {beta : Rel A C}:
 domain alpha ⊆ domain beta <-> alpha ⊆ ((beta ・ beta #) ・ alpha).
Proof.
split; move => H.
apply domain_lemma2a in H.
apply (@inc_trans _ _ _ (alpha ∩ (beta ・ ∇ C B))).
apply (fun H' => @inc_trans _ _ _ _ _ H' (cap_inc_compat_l H)).
replace (alpha ∩ (alpha ・ ∇ B B)) with ((alpha ・ Id B) ∩ (alpha ・ ∇ B B)).
apply (fun H' => @inc_trans _ _ _ _ _ H' (comp_cap_distr_l)).
rewrite cap_universal comp_id_r.
apply inc_refl.
by [rewrite comp_id_r].
rewrite cap_comm comp_assoc.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
rewrite cap_comm cap_universal.
apply inc_refl.
apply domain_inc_compat in H.
apply (@inc_trans _ _ _ _ _ H).
rewrite comp_assoc.
apply comp_domain1.
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_corollary1]
In below figure,
$$
\mbox{``$\alpha$ and $\beta$ are total''} \land \alpha^\sharp \cdot \beta \sqsubseteq \rho^\sharp \cdot \tau \Rightarrow \mbox{``$\alpha \cdot \rho^\sharp \sqcap \beta \cdot \tau^\sharp$ is total''}.
$$
$$
\xymatrix{
& & Y \\
X \ar@{-_>}[rru]^\alpha \ar@{._>}[rr]_{\quad \alpha \rho^\sharp \sqcap \beta \tau^\sharp} \ar@{-_>}[rrd]_\beta & & T \ar@{-_>}[u]_\rho \ar@{-_>}[d]^\tau \\
& & Z \\
}
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_corollary1 {X Y Z T : eqType}
 {alpha : Rel X Y} {beta : Rel X Z} {rho : Rel T Y} {tau : Rel T Z}:
 total_r alpha -> total_r beta -> (alpha # ・ beta) ⊆ (rho # ・ tau) ->
 total_r ((alpha ・ rho #) ∩ (beta ・ tau #)).
Proof.
move => H H0 H1.
move : (comp_inc_compat H H0) => H2.
rewrite comp_id_l -comp_assoc (@comp_assoc _ _ _ _ alpha) in H2.
rewrite /total_r.
replace (Id X) with (((alpha ・ (rho # ・ tau)) ・ beta #) ∩ Id X).
rewrite -comp_assoc comp_assoc.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
rewrite comp_id_l comp_id_r comp_inv comp_inv inv_invol inv_invol.
rewrite inv_cap_distr comp_inv comp_inv inv_invol inv_invol (@cap_comm _ _ (tau ・ beta #)).
apply inc_refl.
apply Logic.eq_sym.
rewrite cap_comm.
apply inc_def1.
apply (@inc_trans _ _ _ _ _ H2).
apply comp_inc_compat_ab_a'b.
apply (comp_inc_compat_ab_ab' H1).
Qed.

(** %
\begin{screen}
\begin{lemma}[domain\_corollary2]
In below figure,
$$
\mbox{``$\alpha$ and $\beta$ are univalent''} \land \rho \cdot \rho^\sharp \sqcap \tau \cdot \tau^\sharp = id_T \Rightarrow \mbox{``$\alpha \cdot \rho^\sharp \sqcap \beta \cdot \tau^\sharp$ is univalent''}.
$$
$$
\xymatrix{
& & Y \\
X \ar@{-_>}[rru]^\alpha \ar@{._>}[rr]_{\quad \alpha \rho^\sharp \sqcap \beta \tau^\sharp} \ar@{-_>}[rrd]_\beta & & T \ar@{-_>}[u]_\rho \ar@{-_>}[d]^\tau \\
& & Z \\
}
$$
\end{lemma}
\end{screen}
% **)
Lemma domain_corollary2 {X Y Z T : eqType}
 {alpha : Rel X Y} {beta : Rel X Z} {rho : Rel T Y} {tau : Rel T Z}:
 univalent_r alpha -> univalent_r beta -> (rho ・ rho #) ∩ (tau ・ tau #) = Id T ->
 univalent_r ((alpha ・ rho #) ∩ (beta ・ tau #)).
Proof.
move => H H0 H1.
rewrite /univalent_r.
rewrite -H1 inv_cap_distr.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_l)).
apply cap_inc_compat.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_l)).
rewrite comp_inv inv_invol -comp_assoc (@comp_assoc _ _ _ _ rho).
apply comp_inc_compat_ab_a'b.
apply (comp_inc_compat_ab_a H).
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply (@inc_trans _ _ _ _ _ (cap_r)).
rewrite comp_inv inv_invol -comp_assoc (@comp_assoc _ _ _ _ tau).
apply comp_inc_compat_ab_a'b.
apply (comp_inc_compat_ab_a H0).
Qed.

(** %
\subsection{矩形関係}
\begin{screen}
$\alpha :A \rel B$ が
$$
\alpha \cdot \nabla_{BA} \cdot \alpha \sqsubseteq \alpha
$$
を満たすとき, $\alpha$ は 矩形関係(rectangular relation)であると言われる.
\end{screen}
% **)
Definition rectangular {A B : eqType} (alpha : Rel A B):=
 ((alpha ・ ∇ B A) ・ alpha) ⊆ alpha.

(** %
\begin{screen}
\begin{lemma}[rectangular\_inv]
Let $\alpha :A \rel B$ is a rectangular relation, then $\alpha^\sharp$ is also a rectangular relation.
\end{lemma}
\end{screen}
% **)
Lemma rectangular_inv {A B : eqType} {alpha : Rel A B}:
 rectangular alpha -> rectangular (alpha #).
Proof.
move => H.
apply inv_inc_move.
rewrite comp_inv comp_inv inv_invol inv_universal -comp_assoc.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[rectangular\_capP, rectangular\_cap]
Let $f(\alpha)$ is always a rectangular relation and $P$ : predicate, then $\sqcap_{P(\beta)} f(\beta)$ is also a rectangular relation.
\end{lemma}
\end{screen}
% **)
Lemma rectangular_capP {A B C D : eqType} {f : Rel C D -> Rel A B} {P : Rel C D -> Prop}:
 (forall alpha : Rel C D, P alpha -> rectangular (f alpha)) -> rectangular (∩_{P} f).
Proof.
move => H.
rewrite /rectangular.
apply (@inc_trans _ _ _ (∩_{P} (fun alpha : Rel C D => (f alpha ・ ∇ B A) ・ f alpha))).
apply (@inc_trans _ _ _ _ _ (comp_capP_distr_l)).
apply inc_capP.
move => beta H0.
apply (@inc_trans _ _ _ (((∩_{P} f) ・ ∇ B A) ・ f beta)).
move : beta H0.
apply inc_capP.
apply inc_refl.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_a'b.
move : H0.
apply inc_capP.
apply inc_refl.
apply inc_capP.
move => beta H0.
apply (fun H' => @inc_trans _ _ _ _ _ H' (H beta H0)).
move : beta H0.
apply inc_capP.
apply inc_refl.
Qed.

Lemma rectangular_cap {A B : eqType} {alpha beta : Rel A B}:
 rectangular alpha -> rectangular beta -> rectangular (alpha ∩ beta).
Proof.
move => H H0.
rewrite (@cap_to_capP _ _ _ _ _ _ id).
apply rectangular_capP.
move => gamma.
case => H1; rewrite H1.
apply H.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[rectangular\_comp]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\alpha$ or $\beta$ is a rectangular relation, then $\alpha \cdot \beta$ is also a rectangular relation.
\end{lemma}
\end{screen}
% **)
Lemma rectangular_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 rectangular alpha \/ rectangular beta -> rectangular (alpha ・ beta).
Proof.
rewrite /rectangular.
case; move => H.
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
rewrite comp_assoc comp_assoc.
apply comp_inc_compat_ab_ab'.
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
rewrite -comp_assoc -comp_assoc.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[rectangular\_unit]
Let $\alpha :A \rel B$. Then,
$$
\mbox{``$\alpha$ is rectangular''} \Leftrightarrow \exists \mu :I \rel A, \exists \rho :I \rel B, \alpha = \rho^\sharp \cdot \mu.
$$
\end{lemma}
\end{screen}
% **)
Lemma rectangular_unit {A B : eqType} {alpha : Rel A B}:
 rectangular alpha <-> exists (mu : Rel i A)(rho : Rel i B), alpha = mu # ・ rho.
Proof.
split; move => H.
exists (∇ i B ・ alpha #).
exists (∇ i A ・ alpha).
rewrite comp_inv inv_invol inv_universal.
rewrite -comp_assoc (@comp_assoc _ _ _ _ alpha) lemma_for_tarski2.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
apply H.
elim H => mu.
elim => rho H0.
rewrite H0.
rewrite /rectangular.
rewrite -comp_assoc.
apply comp_inc_compat_ab_a'b.
rewrite comp_assoc comp_assoc.
apply comp_inc_compat_ab_a.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
Qed.

End main.