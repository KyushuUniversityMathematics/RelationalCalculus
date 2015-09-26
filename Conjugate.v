Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.

(** %
\section{共役性の定義}
\begin{screen}
条件 $P$ を満たす関係 $\alpha :A \rel B$ と条件 $Q$ を満たす関係 $\beta :A' \rel B'$ が変換 $\alpha = \phi (\beta), \beta = \psi (\alpha)$ によって, 1 対 1 (全射的)に対応することを, 図式
$$
\frac{\alpha :A \rel B \,\, \{ P \}}{\beta :A' \rel B' \,\, \{ Q \}} \,\, \frac{\alpha = \phi (\beta)}{\beta = \psi (\alpha)}
$$
によって表す. また, Coq では以下のように表すことにする.
\end{screen}
% **)
Definition conjugate
 (A B C D : eqType) (P : Rel A B -> Prop) (Q : Rel C D -> Prop)
 (phi : Rel C D -> Rel A B) (psi : Rel A B -> Rel C D):=
 (forall alpha : Rel A B, P alpha -> Q (psi alpha) /\ phi (psi alpha) = alpha)
 /\ (forall beta : Rel C D, Q beta -> P (phi beta) /\ psi (phi beta) = beta).

(** %
\begin{screen}
さらに, 上の図式において条件 $P$ または $Q$ が不要な場合には, 以下の \verb|True_r| を代入する.
\end{screen}
% **)
Definition True_r {A B : eqType} := fun _ : Rel A B => True.

(** %
\section{共役の例}
\begin{screen}
\begin{lemma}[inv\_conjugate]
Inverse relation $(^\sharp)$ makes conjugate. That is,
$$
\frac{\alpha :A \rel B}{\beta :B \rel A} \,\, \frac{\alpha = \beta^\sharp}{\beta = \alpha^\sharp}.
$$
\end{lemma}
\end{screen}
% **)
Lemma inv_conjugate {A B : eqType}:
 conjugate A B B A True_r True_r (@inverse _ _) (@inverse _ _).
Proof.
split.
move => alpha H.
split.
by [].
apply inv_invol.
move => beta H.
split.
by [].
apply inv_invol.
Qed.

(** %
\begin{screen}
\begin{lemma}[injection\_conjugate]
Let $j :C \rightarrowtail B$ be an injection. Then,
$$
\frac{f :A \to B \,\, \{ f^\sharp \cdot f \sqsubseteq j^\sharp \cdot j \}}{h :A \to C} \,\, \frac{f=h \cdot j}{h=f \cdot j^\sharp}
$$
\end{lemma}
\end{screen}
% **)
Lemma injection_conjugate {A B C : eqType} {j : Rel C B}:
 injection_r j ->
 conjugate A B A C (fun f : Rel A B => ((f # ・ f) ⊆ (j # ・ j)) /\ function_r f)
 (fun h : Rel A C => function_r h) (fun h : Rel A C => h ・ j) (fun f : Rel A B => f ・ j #).
Proof.
elim.
elim => H H0 H1.
split.
move => alpha.
elim => H2.
elim => H3 H4.
assert (function_r (alpha ・ j #)).
split.
apply (@inc_trans _ _ _ _ _ H3).
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ _ j).
apply (@inc_trans _ _ _ (alpha ・ ((alpha # ・ alpha) ・ alpha #))).
rewrite comp_assoc -comp_assoc.
apply (comp_inc_compat_a_ab H3).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_a'b H2).
apply (fun H' => @inc_trans _ _ _ _ _ H' H1).
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ _ alpha).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_b.
apply (@inc_trans _ _ _ _ _ H2).
apply H0.
split.
apply H5.
apply function_inc.
apply function_comp.
apply H5.
split.
apply H.
apply H0.
split.
apply H3.
apply H4.
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H0.
move => beta.
elim => H2 H3.
assert (function_r (beta ・ j)).
split.
apply (@inc_trans _ _ _ _ _ H2).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ j).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H).
apply (fun H' => @inc_trans _ _ _ _ _ H' H0).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ beta).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H3).
split.
split.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ beta).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H3).
apply H4.
rewrite comp_assoc.
replace (j ・ j #) with (Id C).
apply comp_id_r.
apply inc_antisym.
apply H.
rewrite /univalent_r in H1.
rewrite inv_invol in H1.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[injection\_conjugate\_corollary1, injection\_conjugate\_corollary2]
Let $j :C \rightarrowtail B$ be an injection and $f :A \to B$ be a function. Then,
$$
f^\sharp \cdot f \sqsubseteq j^\sharp \cdot j \Leftrightarrow (\exists !h:A \to C, f=h \cdot j) \Leftrightarrow (\exists h':A \rel C, f \sqsubseteq h' \cdot j).
$$
\end{lemma}
\end{screen}
% **)
Lemma injection_conjugate_corollary1 {A B C : eqType} {f : Rel A B} {j : Rel C B}:
 injection_r j -> function_r f ->
 ((f # ・ f) ⊆ (j # ・ j) <-> exists! h : Rel A C, function_r h /\ f = h ・ j).
Proof.
move => H H0.
move : (@injection_conjugate A _ _ _ H).
elim => H1 H2.
split; move => H3.
exists (f ・ j #).
split.
move : (H1 f (conj H3 H0)).
elim => H4 H5.
split.
apply H4.
by [rewrite H5].
move => h.
elim => H4 H5.
rewrite H5 comp_assoc.
replace (j ・ j #) with (Id C).
apply comp_id_r.
rewrite /injection_r/function_r/univalent_r in H.
rewrite inv_invol in H.
apply inc_antisym.
apply H.
apply H.
elim H3 => h.
elim.
elim => H4 H5 H6.
rewrite H5 comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ h).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_b.
apply H4.
Qed.

Lemma injection_conjugate_corollary2 {A B C : eqType} {f : Rel A B} {j : Rel C B}:
 injection_r j -> function_r f ->
 ((f # ・ f) ⊆ (j # ・ j) <-> exists h' : Rel A C, f ⊆ (h' ・ j)).
Proof.
move => H H0.
split; move => H1.
apply (injection_conjugate_corollary1 H H0) in H1.
elim H1 => h.
elim.
elim => H2 H3 H4.
exists h.
rewrite H3.
apply inc_refl.
elim H1 => h' H2.
replace (f # ・ f) with (f # ・ (f ∩ (h' ・ j))).
apply (@inc_trans _ _ _ ((f # ・ f) ・ (j # ・ j))).
rewrite comp_assoc cap_comm -(@comp_assoc _ _ _ _ f).
apply comp_inc_compat_ab_ab'.
apply (@inc_trans _ _ _ _ _ (@dedekind2 _ _ _ _ _ _)).
apply comp_inc_compat_ab_a'b.
apply cap_r.
apply comp_inc_compat_ab_b.
apply H0.
apply f_equal.
apply inc_def1 in H2.
by [rewrite -H2].
Qed.

(** %
\begin{screen}
\begin{lemma}[surjection\_conjugate]
Let $e :A \twoheadrightarrow C$ be a surjection. Then,
$$
\frac{f :A \to B \,\, \{ e \cdot e^\sharp \sqsubseteq f \cdot f^\sharp \}}{h :C \to B} \,\, \frac{f=e \cdot h}{h=e^\sharp \cdot f}
$$
\end{lemma}
\end{screen}
% **)
Lemma surjection_conjugate {A B C : eqType} {e : Rel A C}:
 surjection_r e ->
 conjugate A B C B (fun f : Rel A B => ((e ・ e #) ⊆ (f ・ f #)) /\ function_r f)
 (fun h : Rel C B => function_r h) (fun h : Rel C B => e ・ h) (fun f : Rel A B => e # ・ f).
Proof.
elim.
elim => H H0 H1.
split.
move => alpha.
elim => H2.
elim => H3 H4.
assert (function_r (e # ・ alpha)).
split.
apply (@inc_trans _ _ _ _ _ H1).
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ alpha).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H3).
apply (fun H' => @inc_trans _ _ _ _ _ H' H4).
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ e).
apply (@inc_trans _ _ _ (alpha # ・ ((alpha ・ alpha #) ・ alpha))).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_a'b H2).
rewrite comp_assoc -comp_assoc.
apply (comp_inc_compat_ab_a H4).
split.
apply H5.
apply Logic.eq_sym.
apply function_inc.
split.
apply H3.
apply H4.
apply function_comp.
split.
apply H.
apply H0.
apply H5.
rewrite -comp_assoc.
apply comp_inc_compat_b_ab.
apply H.
move => beta.
elim => H2 H3.
assert (function_r (e ・ beta)).
split.
apply (@inc_trans _ _ _ _ _ H).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ beta).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H2).
apply (fun H' => @inc_trans _ _ _ _ _ H' H3).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ e).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H0).
split.
split.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ beta).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_b_ab H2).
apply H4.
rewrite -comp_assoc.
replace (e # ・ e) with (Id C).
apply comp_id_l.
apply inc_antisym.
rewrite /total_r in H1.
rewrite inv_invol in H1.
apply H1.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[surjection\_conjugate\_corollary]
Let $e :A \twoheadrightarrow C$ be a surjection and $f :A \to B$ be a function. Then,
$$
e \cdot e^\sharp \sqsubseteq f \cdot f^\sharp \Leftrightarrow (\exists !h:C \to B, f=e \cdot h).
$$
\end{lemma}
\end{screen}
% **)
Lemma surjection_conjugate_corollary {A B C : eqType} {f : Rel A B} {e : Rel A C}:
 surjection_r e -> function_r f ->
 ((e ・ e #) ⊆ (f ・ f #) <-> exists! h : Rel C B, function_r h /\ f = e ・ h).
Proof.
move => H H0.
move : (@surjection_conjugate _ B _ _ H).
elim => H1 H2.
split; move => H3.
exists (e # ・ f).
split.
move : (H1 f (conj H3 H0)).
elim => H4 H5.
split.
apply H4.
by [rewrite H5].
move => h.
elim => H4 H5.
rewrite H5 -comp_assoc.
replace (e # ・ e) with (Id C).
apply comp_id_l.
rewrite /surjection_r/function_r/total_r in H.
rewrite inv_invol in H.
apply inc_antisym.
apply H.
apply H.
elim H3 => h.
elim.
elim => H4 H5 H6.
rewrite H5 comp_inv comp_assoc -(@comp_assoc _ _ _ _ h).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_b_ab.
apply H4.
Qed.

(** %
\begin{screen}
\begin{lemma}[subid\_conjugate]
Subidentity $u \sqsubseteq id_A$ corresponds $\rho :I \rel A$. That is,
$$
\frac{\rho :I \rel A}{u :A \rel A \,\, \{ u \sqsubseteq id_A \}} \,\, \frac{\rho = \nabla_{IA} \cdot u}{u = id_A \sqcap \nabla_{AI} \cdot \rho}.
$$
\end{lemma}
\end{screen}
% **)
Lemma subid_conjugate {A : eqType}:
 conjugate i A A A True_r (fun u : Rel A A => u ⊆ Id A)
 (fun u : Rel A A => ∇ i A ・ u) (fun rho : Rel i A => Id A ∩ (∇ A i ・ rho)).
Proof.
split.
move => alpha H.
split.
apply cap_l.
apply inc_antisym.
apply (@inc_trans _ _ _ (∇ i A ・ (∇ A i ・ alpha))).
apply comp_inc_compat_ab_ab'.
apply cap_r.
rewrite -comp_assoc.
apply comp_inc_compat_ab_b.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
rewrite -(@inv_universal i A).
apply (fun H' => @inc_trans _ _ _ _ _ H' (@dedekind1 _ _ _ _ _ _)).
rewrite comp_id_r cap_comm cap_universal.
apply inc_refl.
move => beta H.
split.
by [].
apply inc_antisym.
rewrite cap_comm -comp_assoc lemma_for_tarski2.
apply (@inc_trans _ _ _ _ _ (@dedekind2 _ _ _ _ _ _)).
rewrite comp_id_l cap_comm cap_universal.
apply comp_inc_compat_ab_b.
rewrite -inv_inc_move inv_id.
apply H.
apply inc_cap.
split.
apply H.
rewrite -comp_assoc.
apply comp_inc_compat_b_ab.
rewrite lemma_for_tarski2.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[subid\_conjugate\_corollary1]
Let $u,v:A \rel A$ and $u,v \sqsubseteq id_A$. Then,
$$
\nabla_{IA} \cdot u = \nabla_{IA} \cdot v \Rightarrow u = v.
$$
\end{lemma}
\end{screen}
% **)
Lemma subid_conjugate_corollary1 {A : eqType} {u v : Rel A A}:
 u ⊆ Id A -> v ⊆ Id A -> ∇ i A ・ u = ∇ i A ・ v -> u = v.
Proof.
move => H H0 H1.
move : (@subid_conjugate A).
elim => H2 H3.
move : (H3 u H).
elim => H4 H5.
rewrite -H5.
move : (H3 v H0).
elim => H6 H7.
rewrite -H7.
apply f_equal.
apply f_equal.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[subid\_conjugate\_corollary2]
Let $\rho, {\rho}' :I \rel A$. Then,
$$
id_A \sqcap \nabla_{AI} \cdot \rho = id_A \sqcap \nabla_{AI} \cdot {\rho}' \Rightarrow \rho = {\rho'}.
$$
\end{lemma}
\end{screen}
% **)
Lemma subid_conjugate_corollary2 {A : eqType} {rho rho' : Rel i A}:
 Id A ∩ (∇ A i ・ rho) = Id A ∩ (∇ A i ・ rho') -> rho = rho'.
Proof.
move => H.
move : (@subid_conjugate A).
elim => H0 H1.
move : (H0 rho I).
elim => H2 H3.
rewrite -H3.
move : (H0 rho' I).
elim => H4 H5.
rewrite -H5.
apply f_equal.
apply H.
Qed.