Require Import Basic_Notations_Set.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.
Require Import Dedekind.
Require Import Logic.IndefiniteDescription.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Module Relation_Properties := Relation_Properties.main def.
Module Functions_Mappings := Functions_Mappings.main def.
Module Dedekind := Dedekind.main def.
Import Basic_Lemmas Relation_Properties Functions_Mappings Dedekind.

(** %
\section{I-点}
\subsection{I-点の定義}
\begin{screen}
Dedekind 圏における域 $X$ のI-点 $x$ とは, 関数 $x:I \rel X$ のことであり, 記号 $x \dot{\in} X$ によって表される. また関係 $\rho :I \rel X$ とI-点 $x:I \rel X$ に対して, 記号 $x \dot{\in} \rho$ で $x \sqsubseteq \rho$ を表すものとする. \\
ちなみにI-点の定義 $x \dot{\in} X$ は $x \dot{\in} \nabla_{IX}$ と言い換えることも可能である.
\end{screen}
% **)
Definition point_inc {X : eqType} (x rho : Rel i X) := function_r x /\ x ⊆ rho.
Definition point {X : eqType} (x : Rel i X) := point_inc x (∇ i X).

(** %
\subsection{I-点の性質}
\begin{screen}
\begin{lemma}[point\_property1]
Let $x,y \dot{\in} X$. Then,
$$
x = y \Leftrightarrow x \cdot y^\sharp = id_I.
$$
\end{lemma}
\end{screen}
% **)
Lemma point_property1 {X : eqType} {x y : Rel i X}:
 point x -> point y -> (x = y <-> x ・ y # = Id i).
Proof.
move => H H0.
split; move => H1.
apply inc_antisym.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
rewrite H1.
apply H0.
apply Logic.eq_sym.
apply function_inc.
apply H0.
apply H.
rewrite -(@comp_id_l _ _ y) -H1 comp_assoc.
apply comp_inc_compat_ab_a.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[point\_property2a, point\_property2b]
Let $\rho :I \rel X$ be a total relation. Then,
$$
\rho \cdot \rho^\sharp = \rho \cdot \nabla_{XI} = id_I.
$$
\end{lemma}
\end{screen}
% **)
Lemma point_property2a {X : eqType} {rho : Rel i X}:
 total_r rho -> rho ・ rho # = Id i.
Proof.
move => H.
apply inc_antisym.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
apply H.
Qed.

Lemma point_property2b {X : eqType} {rho : Rel i X}:
 total_r rho -> rho ・ rho # = rho ・ ∇ X i.
Proof.
move => H.
apply inc_antisym.
apply comp_inc_compat_ab_ab'.
apply inc_alpha_universal.
rewrite (point_property2a H) unit_identity_is_universal.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[point\_property3]
Let $\rho :I \rel X$. Then,
$$
\exists x \dot{\in} \rho \Rightarrow \mbox{``$\rho$ is total''} \land \rho \neq \phi_{IX}.
$$
\end{lemma}
\end{screen}
% **)
Lemma point_property3 {X : eqType} {rho : Rel i X}:
 (exists x : Rel i X, point_inc x rho) -> total_r rho /\ rho <> φ i X.
Proof.
elim => x H.
assert (total_r rho).
elim H => H0 H1.
elim H0 => H2 H3.
apply (@inc_trans _ _ _ _ _ H2).
apply comp_inc_compat.
apply H1.
apply (@inc_inv _ _ _ _ H1).
split.
apply H0.
move => H1.
rewrite /total_r in H0.
rewrite H1 comp_empty_l in H0.
apply unit_identity_not_empty.
apply inc_antisym.
apply H0.
apply inc_empty_alpha.
Qed.

(** %
\begin{screen}
\begin{lemma}[point\_property4]
$$
\exists x \dot{\in} X \Rightarrow \mbox{``$\nabla_{IX}$ is total''} \land \nabla_{IX} \neq \phi_{IX}.
$$
\end{lemma}
\end{screen}
% **)
Lemma point_property4 {X : eqType}:
 (exists x : Rel i X, point x) -> total_r (∇ i X) /\ (∇ i X) <> φ i X.
Proof.
move => H.
apply (@point_property3 _ (∇ i X) H).
Qed.

(** %
\section{I-点に関する諸公理}
\subsection{点公理}
\begin{screen}
この ``点公理'' を使えば, I-点に関する様々な定理や補題が導出できる.
\begin{lemma}[point\_axiom]
Let $\rho :I \rel X$. Then,
$$
\rho = \sqcup_{x \dot{\in} \rho} x.
$$
\end{lemma}
\end{screen}
% **)
Lemma lemma_for_PA {X : eqType} {rho : Rel i X}:
 (((rho = φ i X) -> False) -> False) -> rho = φ i X.
Proof.
move => H.
case (@unit_empty_or_universal (rho ・ rho #)) => H0.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
rewrite H0 comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
apply False_ind.
apply H.
move => H1.
rewrite H1 comp_empty_l in H0.
apply (unit_empty_not_universal H0).
Qed.

Lemma point_axiom {X : eqType} {rho : Rel i X}:
 rho = ∪_{fun x : Rel i X => point_inc x rho} id.
Proof.
apply inc_antisym.
apply bool_lemma2.
assert ((exists x : Rel i X, point_inc x ((∪_{fun x : Rel i X => point_inc x rho} id) ∩ (∪_{fun x : Rel i X => point_inc x rho} id) ^)) -> False).
move => H.
move : (point_property3 H) => H0.
apply H0.
apply cap_complement_empty.
assert ((exists x : Rel i X, point_inc x (rho ∩ (∪_{fun x : Rel i X => point_inc x rho} id) ^)) -> False).
move => H0.
apply H.
elim H0 => x H1.
exists x.
split.
apply H1.
apply inc_cap.
split.
assert (point_inc x rho).
split.
apply H1.
elim H1 => H2 H3.
apply inc_cap in H3.
apply H3.
clear H1.
move : x H2.
apply inc_cupP.
apply inc_refl.
elim H1 => H2 H3.
apply inc_cap in H3.
apply H3.
apply lemma_for_PA.
move => H1.
apply H0.
apply axiom_of_choice.
rewrite /total_r.
remember (rho ∩ (∪_{fun x : Rel i X => point_inc x rho} id) ^) as rho'.
case (@unit_empty_or_universal (rho' ・ rho' #)) => H2.
apply False_ind.
apply H1.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
rewrite H2 comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
rewrite H2.
apply inc_alpha_universal.
apply inc_cupP.
move => beta H.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[PA\_corollary1]
$$
\nabla_{IX} = \sqcup_{x \dot{\in} X} x.
$$
\end{lemma}
\end{screen}
% **)
Lemma PA_corollary1 {X : eqType}: ∇ i X = ∪_{point} id.
Proof.
apply point_axiom.
Qed.

(** %
\begin{screen}
\begin{lemma}[PA\_corollary2]
$$
id_X = \sqcup_{x \dot{\in} X} x^\sharp \cdot x.
$$
\end{lemma}
\end{screen}
% **)
Lemma PA_corollary2 {X : eqType}:
 Id X = ∪_{point} (fun x : Rel i X => x # ・ x).
Proof.
rewrite -(@cap_universal _ _ (Id X)) -lemma_for_tarski2 PA_corollary1.
rewrite comp_cupP_distr_l cap_cupP_distr_l.
apply cupP_eq.
move => alpha H.
apply inc_antisym.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind2)).
rewrite comp_id_l cap_comm cap_universal.
apply inc_refl.
apply inc_cap.
split.
apply H.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[PA\_corollary3]
Let $\alpha , \beta :X \rel Y$. Then,
$$
(\forall x \dot{\in} X, x \cdot \alpha = x \cdot \beta) \Rightarrow \alpha = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma PA_corollary3 {X Y : eqType} {alpha beta : Rel X Y}:
 (forall x : Rel i X, point x -> x ・ alpha = x ・ beta) -> alpha = beta.
Proof.
move => H.
rewrite -(@comp_id_l _ _ alpha) -(@comp_id_l _ _ beta) PA_corollary2.
rewrite comp_cupP_distr_r comp_cupP_distr_r.
apply cupP_eq.
move => gamma H0.
by [rewrite comp_assoc comp_assoc (H gamma H0)].
Qed.

(** %
\begin{screen}
\begin{lemma}[PA\_corollary4]
Let $\alpha :X \rel Y$. Then,
$$
\mbox{``$\alpha$ is total''} \Leftrightarrow \forall x \dot{\in} X, \mbox{``$x \cdot \alpha$ is total''}.
$$
\end{lemma}
\end{screen}
% **)
Lemma PA_corollary4 {X Y : eqType} {alpha : Rel X Y}:
 total_r alpha <-> forall x : Rel i X, point x -> total_r (x ・ alpha).
Proof.
split; move => H.
move => x H0.
apply total_comp.
apply H0.
apply H.
rewrite /total_r.
rewrite PA_corollary2.
apply inc_cupP.
move => x H0.
move : (H x H0) => H1.
apply (@inc_trans _ _ _ ((x # ・ ((x ・ alpha) ・ (x ・ alpha) #)) ・ x)).
apply comp_inc_compat_ab_a'b.
apply (comp_inc_compat_a_ab H1).
rewrite comp_inv -comp_assoc -comp_assoc -comp_assoc.
rewrite comp_assoc (@comp_assoc _ _ _ _ (x # ・ x)).
apply (@inc_trans _ _ _ ((x # ・ x) ・ (alpha ・ alpha #))).
apply comp_inc_compat_ab_a.
apply H0.
apply comp_inc_compat_ab_b.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[PA\_corollary5]
Let $\alpha :X \rel Y$. Then,
$$
\mbox{``$\alpha$ is univalent''} \Leftrightarrow \forall x \dot{\in} X, \mbox{``$x \cdot \alpha$ is univalent''}.
$$
\end{lemma}
\end{screen}
% **)
Lemma PA_corollary5 {X Y : eqType} {alpha : Rel X Y}:
 univalent_r alpha <-> forall x : Rel i X, point x -> univalent_r (x ・ alpha).
Proof.
split; move => H.
move => x H0.
apply univalent_comp.
apply H0.
apply H.
rewrite /univalent_r.
rewrite -(@comp_id_r _ _ (alpha #)) PA_corollary2.
rewrite comp_cupP_distr_l comp_cupP_distr_r.
apply inc_cupP.
move => x H0.
move : (H x H0) => H1.
rewrite -comp_assoc -comp_inv comp_assoc.
apply H1.
Qed.

(** %
\subsection{全域性公理}
\begin{screen}
\begin{lemma}[total\_axiom]
Let $\rho :I \rel X$. Then,
$$
\rho \neq \phi_{IX} \Rightarrow id_I = \rho \cdot \rho^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma total_axiom {X : eqType} {rho : Rel i X}:
 rho <> φ i X -> Id i = rho ・ rho #.
Proof.
move => H.
case (@unit_empty_or_universal (rho ・ rho #)) => H0.
apply False_ind.
apply H.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
rewrite H0 comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
by [rewrite H0 unit_identity_is_universal].
Qed.

(** %
\begin{screen}
\begin{lemma}[Tot\_corollary1]
Let $\rho :I \rel X$ and $x \dot{\in} X$. Then,
$$
\rho \sqsubseteq x \Rightarrow \rho = \phi_{IX} \lor \rho = x.
$$
\end{lemma}
\end{screen}
% **)
Lemma Tot_corollary1 {X : eqType} {rho x : Rel i X}:
 point x -> rho ⊆ x -> rho = φ i X \/ rho = x.
Proof.
move => H H0.
case (@unit_empty_or_universal (rho ・ rho #)) => H1.
left.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (relation_rel_inv_rel)).
rewrite H1 comp_empty_l.
apply inc_refl.
apply inc_empty_alpha.
right.
apply inc_antisym.
apply H0.
rewrite -(@comp_id_l _ _ x) unit_identity_is_universal -H1 comp_assoc.
apply (@inc_trans _ _ _ (rho ・ (x # ・ x))).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_a'b.
apply (@inc_inv _ _ _ _ H0).
apply comp_inc_compat_ab_a.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[Tot\_corollary2]
Let $x,y \dot{\in} X$. Then,
$$
x \neq y \Leftrightarrow x \cdot y^\sharp = \phi_{II}.
$$
\end{lemma}
\end{screen}
% **)
Lemma Tot_corollary2 {X : eqType} {x y : Rel i X}:
 point x -> point y -> (x <> y <-> x ・ y # = φ i i).
Proof.
move => H H0.
assert (x = y <-> x ・ y # <> φ i i).
rewrite (point_property1 H H0).
split; move => H1.
rewrite H1.
apply unit_identity_not_empty.
case (@unit_empty_or_universal (x ・ y #)) => H2.
apply False_ind.
apply (H1 H2).
by [rewrite H2 unit_identity_is_universal].
rewrite H1.
split; move => H2.
apply (lemma_for_PA H2).
move => H3.
apply (H3 H2).
Qed.

(** %
\begin{screen}
\begin{lemma}[Tot\_corollary3]
Let $f:(I \rel X) \to (I \rel Y)$. Then,
$$
(\forall x \dot{\in} X, \mbox{``$f(x)$ is a function''}) \Rightarrow \mbox{``$\sqcup_{x \dot{\in} X} x^\sharp \cdot f(x)$ is a function''}.
$$
\end{lemma}
\end{screen}
% **)
Lemma Tot_corollary3 {X Y : eqType} {f : Rel i X -> Rel i Y}:
 (forall x : Rel i X, point x -> function_r (f x)) -> function_r (∪_{point} (fun x : Rel i X => x # ・ f x)).
Proof.
move => H.
assert (forall x : Rel i X, point x -> x ・ (∪_{point} (fun x0 : Rel i X => x0 # ・ f x0)) = f x).
move => x H0.
assert (x ・ x # = Id i).
apply inc_antisym.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
apply H0.
rewrite -(@comp_id_l _ _ (f x)) -H1.
apply inc_antisym.
rewrite comp_cupP_distr_l.
apply inc_cupP.
move => y H2.
rewrite -comp_assoc.
case (@unit_empty_or_universal (x ・ y #)) => H3.
rewrite H3 comp_empty_l.
apply inc_empty_alpha.
rewrite -unit_identity_is_universal in H3.
apply (point_property1 H0 H2) in H3.
rewrite H3.
apply inc_refl.
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
clear H1.
move : x H0.
apply inc_cupP.
apply inc_refl.
split.
rewrite PA_corollary4.
move => x H1.
rewrite (H0 x H1).
apply (H x H1).
rewrite PA_corollary5.
move => x H1.
rewrite (H0 x H1).
apply (H x H1).
Qed.

(** %
\subsection{その他の公理}
\begin{screen}
\begin{lemma}[nonempty\_axiom]
Let $\rho :I \rel X$. Then,
$$
\rho \neq \phi_{IX} \Rightarrow \exists x \dot{\in} \rho.
$$
\end{lemma}
\end{screen}
% **)
Lemma nonempty_axiom {X : eqType} {rho : Rel i X}:
 rho <> φ i X -> exists x : Rel i X, point_inc x rho.
Proof.
move : (@axiom_of_choice _ _ rho) => H.
move => H0.
apply H.
rewrite /total_r.
rewrite (total_axiom H0).
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[axiom\_of\_subobjects2]
Let $\rho :I \rel X$. Then,
$$
\exists S, \exists j:S \rel X, \rho = \nabla_{IS} \cdot j \land j \cdot j^\sharp = id_S.
$$
\end{lemma}
\end{screen}
% **)
Lemma axiom_of_subobjects2 {X : eqType} {rho : Rel i X}:
 exists (S : eqType)(j : Rel S X), rho = ∇ i S ・ j /\ j ・ j # = Id S.
Proof.
elim (@rationality _ _ rho) => R.
elim => f.
elim => g.
elim => H.
elim => H0.
elim => H1 H2.
exists R.
exists g.
split.
rewrite H1.
apply inc_antisym.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
apply comp_inc_compat_ab_a'b.
apply (@inc_trans _ _ _ (∇ i R ・ (f ・ f #))).
apply comp_inc_compat_a_ab.
apply H.
rewrite -comp_assoc.
apply comp_inc_compat_ab_b.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
rewrite -H2 cap_comm inc_def1.
assert ((f # ・ g) ⊆ rho).
rewrite H1.
apply inc_refl.
apply (function_move1 H) in H3.
apply (@inc_trans _ _ _ ((f ・ rho) ・ (f ・ rho) #)).
apply comp_inc_compat.
apply H3.
apply (@inc_inv _ _ _ _ H3).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ rho).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_b.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
Qed.

(** %
\section{その他の補題}
\begin{screen}
\begin{lemma}[point\_atomic]
Let $x \dot{\in} X$, then $x$ is atomic.
\end{lemma}
\end{screen}
% **)
Lemma point_atomic {X : eqType} {x : Rel i X}: point x -> atomic x.
Proof.
move => H.
split.
move : (@point_property3 X x) => H0.
apply H0.
exists x.
split.
apply H.
apply inc_refl.
move => beta.
apply (Tot_corollary1 H).
Qed.

(** %
\begin{screen}
\begin{lemma}[point\_atomic2]
Let $x \dot{\in} X$ and $y \dot{\in} Y$, then $x^\sharp \cdot y$ is atomic.
\end{lemma}
\end{screen}
% **)
Lemma point_atomic2 {X Y : eqType} {x : Rel i X} {y : Rel i Y}:
 point x -> point y -> atomic (x # ・ y).
Proof.
move => H H0.
split.
move => H1.
assert (Id i = (x ・ x #) ・ (y ・ y #)).
apply inc_antisym.
rewrite -(@comp_id_l _ _ (Id i)).
apply comp_inc_compat.
apply H.
apply H0.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
rewrite comp_assoc -(@comp_assoc _ _ _ _ (x #)) in H2.
rewrite H1 comp_empty_l comp_empty_r in H2.
apply (unit_identity_not_empty H2).
move => beta H1.
case (@unit_empty_or_universal ((∇ i X ・ beta) ・ ∇ Y i)) => H2.
left.
apply inc_antisym.
replace (φ X Y) with ((∇ X i ・ φ i i) ・ ∇ i Y).
rewrite -H2 -comp_assoc -comp_assoc unit_universal.
rewrite comp_assoc unit_universal.
apply (@inc_trans _ _ _ (∇ X X ・ beta)).
apply comp_inc_compat_b_ab.
apply inc_alpha_universal.
apply comp_inc_compat_a_ab.
apply inc_alpha_universal.
by [rewrite comp_empty_r comp_empty_l].
apply inc_empty_alpha.
right.
apply inc_antisym.
apply H1.
assert (beta <> φ X Y).
move => H3.
rewrite H3 comp_empty_r comp_empty_l in H2.
apply (unit_empty_not_universal H2).
apply (@inc_trans _ _ _ (x # ・ (x ・ beta))).
apply comp_inc_compat_ab_ab'.
assert ((x ・ beta) ⊆ y).
apply (@inc_trans _ _ _ (x ・ (x # ・ y))).
apply (comp_inc_compat_ab_ab' H1).
rewrite -comp_assoc.
apply comp_inc_compat_ab_b.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
apply inc_def1 in H1.
rewrite H1 in H3.
assert (x # ・ ((x ・ beta) ∩ y) <> φ X Y).
move => H5.
apply H3.
apply inc_antisym.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (dedekind1)).
rewrite cap_comm inv_invol H5.
apply inc_refl.
apply inc_empty_alpha.
case (Tot_corollary1 H0 H4) => H6.
rewrite H6 cap_comm cap_empty comp_empty_r in H5.
apply False_ind.
by [apply H5].
rewrite H6.
apply inc_refl.
rewrite -comp_assoc.
apply comp_inc_compat_ab_b.
apply H.
Qed.

End main.