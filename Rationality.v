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
\exists R, \exists j:R \rightarrowtail A, u = j^\sharp \cdot j.
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
\exists e:A \twoheadrightarrow R, \exists m:R \rightarrowtail B, f = e \cdot m.
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

(** %
\begin{screen}
\begin{lemma}[axiom\_of\_subobjects]
Let $u :A \rel A$ and $u \sqsubseteq id_A$. Then,
$$
\exists R, \exists j:R \to A, j^\sharp \cdot j = u \land j \cdot j^\sharp = id_R.
$$
\end{lemma}
\end{screen}
% **)
Lemma axiom_of_subobjects {A : eqType} {u : Rel A A}:
 u ⊆ Id A -> exists (R : eqType)(j : Rel R A), j # ・ j = u /\ j ・ j # = Id R.
Proof.
move => H.
elim (rationality_corollary1 H) => R.
elim => j H0.
exists R.
exists j.
split.
apply Logic.eq_sym.
apply H0.
apply inc_antisym.
replace (j ・ j #) with ((j #) # ・ j #).
apply H0.
by [rewrite inv_invol].
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[square\_diagram]
In below figure,
$$
f \cdot x = g \cdot y \Leftrightarrow f^\sharp \cdot g \sqsubseteq x \cdot y^\sharp.
$$
$$
\xymatrix{
X \ar@{->}[r]^f \ar@{->}[d]_g & A \ar@{->}[d]^x \\
B \ar@{->}[r]_y & D
}
$$
\end{lemma}
\end{screen}
% **)
Lemma square_diagram {X A B D : eqType}
 {f : Rel X A} {g : Rel X B} {x : Rel A D} {y : Rel B D}:
 function_r f -> function_r g -> function_r x -> function_r y ->
 (f ・ x = g ・ y <-> (f # ・ g) ⊆ (x ・ y #)).
Proof.
move => H H0 H1 H2.
split; move => H3.
rewrite -(function_move1 H) -comp_assoc -(function_move2 H2) H3.
apply inc_refl.
apply Logic.eq_sym.
apply function_inc.
apply (function_comp H0 H2).
apply (function_comp H H1).
rewrite (function_move2 H2) comp_assoc (function_move1 H).
apply H3.
Qed.