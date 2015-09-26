Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Functions_Mappings.

(** %
\section{有理性から導かれる系}
\begin{screen}
\begin{lemma}[rationality\_corollary1]
Let $u :A \rel A$ and $u \sqsubseteq id_A$. Then,
$$
\exists R, \exists j:R \rightarrowtail A, u=j^\sharp \cdot j.
$$
\end{lemma}
\end{screen}
% **)
Lemma rationality_corollary1 {A : eqType} {u : Rel A A}:
 u ⊆ Id A -> exists (R : eqType)(j : Rel R A), injection_r j /\ u = j # ・ j.
Proof.
move : (rationality _ _ u).
elim => R.
elim => f.
elim => g.
elim => H.
elim => H0.
elim => H1 H2 H3.
exists R.
exists f.
assert (g = f).
apply (function_inc H0 H).
apply (@inc_trans _ _ _ ((f ・ f #) ・ g)).
apply comp_inc_compat_b_ab.
apply H.
rewrite comp_assoc -H1.
apply (comp_inc_compat_ab_a H3).
rewrite H4 in H1.
rewrite H4 cap_idem in H2.
split.
split.
apply H.
rewrite /univalent_r.
rewrite inv_invol H2.
apply inc_refl.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[rationality\_corollary2]
Let $f :A \to B$ be a function. Then,
$$
\exists e:A \twoheadrightarrow R, \exists m:R \rightarrowtail B, f=e \cdot m.
$$
\end{lemma}
\end{screen}
% **)
Lemma rationality_corollary2 {A B : eqType} {f : Rel A B}:
 function_r f -> exists (R : eqType)(e : Rel A R)(m : Rel R B), surjection_r e /\ injection_r m.
Proof.
elim => H H0.
move : (@rationality_corollary1 _ (f # ・ f) H0).
elim => R.
elim => m.
elim => H1 H2.
exists R.
exists (f ・ m #).
exists m.
split.
apply (injection_unique2 H1 (conj H H0) H2).
apply H1.
Qed.