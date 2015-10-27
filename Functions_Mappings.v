Require Import Basic_Notations.
Require Import Basic_Lemmas.
Require Import Relation_Properties.
Require Import Logic.FunctionalExtensionality.

(** %
\section{全域性, 一価性, 写像に関する補題}
\begin{screen}
\begin{lemma}[id\_function]
$id_A :A \rel A$ is a function.
\end{lemma}
\end{screen}
% **)
Lemma id_function {A : eqType}: function_r (Id A).
Proof.
rewrite /function_r/total_r/univalent_r.
rewrite inv_id comp_id_l.
split.
apply inc_refl.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[unit\_function]
$\nabla_{AI} :A \rel I$ is a function.
\end{lemma}
\end{screen}
% **)
Lemma unit_function {A : eqType}: function_r (∇ A i).
Proof.
rewrite /function_r/total_r/univalent_r.
rewrite inv_universal lemma_for_tarski2 unit_identity_is_universal.
split.
apply inc_alpha_universal.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[total\_comp]
Let $\alpha :A \rel B$ and $\beta :B \rel C$ be total relations, then $\alpha \cdot \beta$ is also a total relation.
\end{lemma}
\end{screen}
% **)
Lemma total_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 total_r alpha -> total_r beta -> total_r (alpha ・ beta).
Proof.
rewrite /total_r.
move => H H0.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ beta).
apply (@inc_trans _ _ _ _ _ H).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_b_ab.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[univalent\_comp]
Let $\alpha :A \rel B$ and $\beta :B \rel C$ be univalent relations, then $\alpha \cdot \beta$ is also a univalent relation.
\end{lemma}
\end{screen}
% **)
Lemma univalent_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r alpha -> univalent_r beta -> univalent_r (alpha ・ beta).
Proof.
rewrite /univalent_r.
move => H H0.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ (alpha #)).
apply (fun H' => @inc_trans _ _ _ _ _ H' H0).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_b.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_comp]
Let $\alpha :A \to B$ and $\beta :B \to C$ be functions, then $\alpha \cdot \beta$ is also a function.
\end{lemma}
\end{screen}
% **)
Lemma function_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 function_r alpha -> function_r beta -> function_r (alpha ・ beta).
Proof.
elim => H H0.
elim => H1 H2.
split.
apply (total_comp H H1).
apply (univalent_comp H0 H2).
Qed.

(** %
\begin{screen}
\begin{lemma}[total\_comp2]
Let $\alpha :A \rel B$, $\beta :B \rel C$ and $\alpha \cdot \beta$ be a total relation, then $\alpha$ is also a total relation.
\end{lemma}
\end{screen}
% **)
Lemma total_comp2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 total_r (alpha ・ beta) -> total_r alpha.
Proof.
move => H.
apply inc_def1 in H.
rewrite comp_inv cap_comm comp_assoc in H.
rewrite /total_r.
rewrite H.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
apply comp_inc_compat.
apply cap_l.
rewrite comp_id_r.
apply cap_r.
Qed.

(** %
\begin{screen}
\begin{lemma}[univalent\_comp2]
Let $\alpha :A \rel B$, $\beta :B \rel C$, $\alpha \cdot \beta$ be a univalent relation and $\alpha^\sharp$ be a total relation, then $\beta$ is a univalent relation.
\end{lemma}
\end{screen}
% **)
Lemma univalent_comp2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r (alpha ・ beta) -> total_r (alpha #) -> univalent_r beta.
Proof.
move => H H0.
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ alpha).
apply comp_inc_compat_ab_ab'.
rewrite /total_r in H0.
rewrite inv_invol in H0.
apply (comp_inc_compat_b_ab H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[total\_inc]
Let $\alpha :A \rel B$ be a total relation and $\alpha \sqsubseteq \beta$, then $\beta$ is also a total relation.
\end{lemma}
\end{screen}
% **)
Lemma total_inc {A B : eqType} {alpha beta : Rel A B}:
 total_r alpha -> alpha ⊆ beta -> total_r beta.
Proof.
move => H H0.
apply (@inc_trans _ _ _ _ _ H).
apply comp_inc_compat.
apply H0.
apply (@inc_inv _ _ _ _ H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[univalent\_inc]
Let $\alpha :A \rel B$ be a univalent relation and $\beta \sqsubseteq \alpha$, then $\beta$ is also a univalent relation.
\end{lemma}
\end{screen}
% **)
Lemma univalent_inc {A B : eqType} {alpha beta : Rel A B}:
 univalent_r alpha -> beta ⊆ alpha -> univalent_r beta.
Proof.
move => H H0.
apply (fun H' => @inc_trans _ _ _ _ _ H' H).
apply comp_inc_compat.
apply (@inc_inv _ _ _ _ H0).
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_inc]
Let $\alpha , \beta :A \to B$ be functions and $\alpha \sqsubseteq \beta$. Then,
$$
\alpha = \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_inc {A B : eqType} {alpha beta : Rel A B}:
 function_r alpha -> function_r beta -> alpha ⊆ beta -> alpha = beta.
Proof.
move => H H0 H1.
apply inc_antisym.
apply H1.
apply (@inc_trans _ _ _ ((alpha ・ alpha #) ・ beta)).
apply comp_inc_compat_b_ab.
apply H.
move : (@inc_inv _ _ _ _ H1) => H2.
apply (@inc_trans _ _ _ ((alpha ・ beta #) ・ beta)).
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
apply H2.
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[total\_universal]
If $\nabla_{IB}$ be a total relation, then
$$
\nabla_{AB} \cdot \nabla_{BC} = \nabla_{AC}.
$$
\end{lemma}
\end{screen}
% **)
Lemma total_universal {A B C : eqType}:
 total_r (∇ i B) -> ∇ A B ・ ∇ B C = ∇ A C.
Proof.
move => H.
rewrite -(@lemma_for_tarski2 A B) -(@lemma_for_tarski2 B C).
rewrite comp_assoc -(@comp_assoc _ _ _ _ (∇ i B)).
replace (∇ i B ・ ∇ B i) with (Id i).
rewrite comp_id_l.
apply lemma_for_tarski2.
apply inc_antisym.
rewrite /total_r in H.
rewrite inv_universal in H.
apply H.
rewrite unit_identity_is_universal.
apply inc_alpha_universal.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_rel\_inv\_rel]
Let $\alpha :A \to B$ be function. Then,
$$
\alpha \cdot \alpha^\sharp \cdot \alpha = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_rel_inv_rel {A B : eqType} {alpha : Rel A B}:
 function_r alpha -> (alpha ・ alpha #) ・ alpha = alpha.
Proof.
move => H.
apply inc_antisym.
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H.
apply comp_inc_compat_b_ab.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_capP\_distr]
Let $f:A \to B,g:D \to C$ be functions, $\theta :(E \rel F) \to (B \rel C)$ and $P$ : predicate. Then,
$$
f \cdot (\sqcap_{P(\theta)} \theta(\alpha)) \cdot g^\sharp = \sqcap_{P(\alpha)} (f \cdot \theta(\alpha) \cdot g^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma function_capP_distr {A B C D E F : eqType}
 {f : Rel A B} {g : Rel D C} {theta : Rel E F -> Rel B C} {P : Rel E F -> Prop}:
 function_r f -> function_r g ->
 (f ・ (∩_{P} theta)) ・ g # =
 ∩_{P} (fun alpha : Rel E F => (f ・ theta alpha) ・ g #).
Proof.
elim => H H0.
elim => H1 H2.
apply inc_antisym.
apply comp_capP_distr.
apply (@inc_trans _ _ _ (((f ・ f #) ・ ∩_{P} (fun alpha : Rel E F => (f ・ theta alpha) ・ g #)) ・ (g ・ g #))).
apply (@inc_trans _ _ _ ((f ・ f #) ・ (∩_{P} (fun alpha : Rel E F => (f ・ theta alpha) ・ g #)))).
apply (comp_inc_compat_b_ab H).
apply (comp_inc_compat_a_ab H1).
rewrite (@comp_assoc _ _ _ _ _ (f #)) comp_assoc -(@comp_assoc _ _ _ _ _ g) -comp_assoc.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_ab_ab'.
apply (@inc_trans _ _ _ (∩_{P} (fun alpha : Rel E F => (f # ・ ((f ・ theta alpha) ・ g #)) ・ g))).
apply comp_capP_distr.
replace (fun alpha : Rel E F => (f # ・ ((f ・ theta alpha) ・ g #)) ・ g) with (fun alpha : Rel E F => ((f # ・ f) ・ theta alpha) ・ (g # ・ g)).
apply inc_capP.
move => beta H3.
apply (@inc_trans _ _ _ ((f # ・ f) ・ theta beta)).
apply (@inc_trans _ _ _ (((f # ・ f) ・ theta beta) ・ (g # ・ g))).
move : beta H3.
apply inc_capP.
apply inc_refl.
apply (comp_inc_compat_ab_a H2).
apply (comp_inc_compat_ab_b H0).
apply functional_extensionality.
move => x.
by [rewrite comp_assoc comp_assoc comp_assoc comp_assoc comp_assoc].
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_cap\_distr, function\_cap\_distr\_l, function\_cap\_distr\_r]
Let $f:A \to B,g:D \to C$ be functions and $\alpha, \beta :B \rel C$. Then,
$$
f \cdot (\alpha \sqcap \beta) \cdot g^\sharp = (f \cdot \alpha \cdot g^\sharp) \sqcap (f \cdot \beta \cdot g^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma function_cap_distr
 {A B C D : eqType} {f : Rel A B} {alpha beta : Rel B C} {g : Rel D C}:
 function_r f -> function_r g ->
 (f ・ (alpha ∩ beta)) ・ g # = ((f ・ alpha) ・ g #) ∩ ((f ・ beta) ・ g #).
Proof.
rewrite (@cap_to_capP _ _ _ _ _ _ id) (@cap_to_capP _ _ _ _ _ _ (fun x => (f ・ x) ・ g #)).
apply function_capP_distr.
Qed.

Lemma function_cap_distr_l
 {A B C : eqType} {f : Rel A B} {alpha beta : Rel B C}:
 function_r f ->
 f ・ (alpha ∩ beta) = (f ・ alpha) ∩ (f ・ beta).
Proof.
move : (@id_function C) => H.
move => H0.
apply (@function_cap_distr _ _ _ _ f alpha beta) in H.
rewrite inv_id comp_id_r comp_id_r comp_id_r in H.
apply H.
apply H0.
Qed.

Lemma function_cap_distr_r
 {B C D : eqType} {alpha beta : Rel B C} {g : Rel D C}:
 function_r g ->
 (alpha ∩ beta) ・ g # = (alpha ・ g #) ∩ (beta ・ g #).
Proof.
move : (@id_function B) => H.
move => H0.
apply (@function_cap_distr _ _ _ _ _ alpha beta g) in H.
rewrite comp_id_l comp_id_l comp_id_l in H.
apply H.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_move1]
Let $\alpha :A \to B$ be a function, $\beta :B \rel C$ and $\gamma :A \rel C$. Then,
$$
\gamma \sqsubseteq \alpha \cdot \beta \Leftrightarrow \alpha^\sharp \cdot \gamma \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_move1 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 function_r alpha -> (gamma ⊆ (alpha ・ beta) <-> (alpha # ・ gamma) ⊆ beta).
Proof.
move => H.
split; move => H0.
apply (@inc_trans _ _ _ ((alpha # ・ alpha) ・ beta)).
rewrite comp_assoc.
apply (comp_inc_compat_ab_ab' H0).
apply comp_inc_compat_ab_b.
apply H.
apply (@inc_trans _ _ _ ((alpha ・ alpha #) ・ gamma)).
apply comp_inc_compat_b_ab.
apply H.
rewrite comp_assoc.
apply (comp_inc_compat_ab_ab' H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_move2]
Let $\beta :B \to C$ be a function, $\alpha :A \rel B$ and $\gamma :A \rel C$. Then,
$$
\alpha \cdot \beta \sqsubseteq \gamma \Leftrightarrow \alpha \sqsubseteq \gamma \cdot \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_move2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 function_r beta -> ((alpha ・ beta) ⊆ gamma <-> alpha ⊆ (gamma ・ beta #)).
Proof.
move => H.
split; move => H0.
apply (@inc_trans _ _ _ ((alpha ・ beta) ・ beta #)).
rewrite comp_assoc.
apply comp_inc_compat_a_ab.
apply H.
apply (comp_inc_compat_ab_a'b H0).
apply (@inc_trans _ _ _ ((gamma ・ beta #) ・ beta)).
apply (comp_inc_compat_ab_a'b H0).
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_rpc\_distr]
Let $f:A \to B,g:D \to C$ be functions and $\alpha, \beta :B \rel C$. Then,
$$
f \cdot (\alpha \Rightarrow \beta) \cdot g^\sharp = (f \cdot \alpha \cdot g^\sharp) \Rightarrow (f \cdot \beta \cdot g^\sharp).
$$
\end{lemma}
\end{screen}
% **)
Lemma function_rpc_distr
 {A B C D : eqType} {f : Rel A B} {alpha beta : Rel B C} {g : Rel D C}:
 function_r f -> function_r g ->
 (f ・ (alpha >> beta)) ・ g # = ((f ・ alpha) ・ g #) >> ((f ・ beta) ・ g #).
Proof.
move => H H0.
apply inc_lower.
move => gamma.
split; move => H1.
apply inc_rpc.
apply (function_move2 H0).
apply (function_move1 H).
apply (@inc_trans _ _ _ (((f # ・ gamma) ・ g) ∩ ((f # ・ ((f ・ alpha) ・ g #)) ・ g))).
rewrite -comp_assoc.
apply (fun H' => @inc_trans _ _ _ _ _ H' (@comp_cap_distr_r _ _ _ _ _ _)).
apply comp_inc_compat_ab_a'b.
apply comp_cap_distr_l.
apply (function_move2 H0) in H1.
apply (function_move1 H) in H1.
rewrite -inc_rpc comp_assoc.
apply (@inc_trans _ _ _ _ _ H1).
apply rpc_inc_compat_r.
rewrite comp_assoc comp_assoc comp_assoc -comp_assoc.
apply (@inc_trans _ _ _ (alpha ・ (g # ・ g))).
apply comp_inc_compat_ab_b.
apply H.
apply comp_inc_compat_ab_a.
apply H0.
apply (function_move2 H0).
apply (function_move1 H).
apply inc_rpc.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
apply (@inc_trans _ _ _ (f # ・ ((gamma ・ g) ∩ ((f #) # ・ alpha)))).
apply comp_inc_compat_ab_a'b.
apply cap_l.
rewrite inv_invol.
apply (@inc_trans _ _ _ ((f # ・ (gamma ∩ ((f ・ alpha) ・ g #))) ・ g)).
rewrite comp_assoc.
apply comp_inc_compat_ab_ab'.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
apply comp_inc_compat_ab_ab'.
apply cap_l.
apply (function_move2 H0).
apply (function_move1 H).
rewrite -inc_rpc -comp_assoc.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_inv\_rel1, function\_inv\_rel2]
Let $f:A \to B$ be a function. Then,
$$
f^\sharp \cdot f = id_B \sqcap f^\sharp \cdot \nabla_{AA} \cdot f = id_B \sqcap \nabla_{BA} \cdot f.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_inv_rel1 {A B : eqType} {f : Rel A B}:
 function_r f -> f # ・ f = Id B ∩ ((f # ・ ∇ A A) ・ f).
Proof.
move => H.
apply inc_antisym.
apply inc_cap.
split.
apply H.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat_a_ab.
apply inc_alpha_universal.
apply (@inc_trans _ _ _ (Id B ∩ (∇ B A ・ f))).
apply cap_inc_compat_l.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
rewrite comp_id_l comp_id_r cap_comm inv_universal.
rewrite cap_universal cap_universal.
apply inc_refl.
Qed.

Lemma function_inv_rel2 {A B : eqType} {f : Rel A B}:
 function_r f -> f # ・ f = Id B ∩ (∇ B A ・ f).
Proof.
move => H.
apply inc_antisym.
rewrite (@function_inv_rel1 _ _ _ H).
apply cap_inc_compat_l.
apply comp_inc_compat_ab_a'b.
apply inc_alpha_universal.
rewrite cap_comm.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
rewrite comp_id_l comp_id_r cap_comm inv_universal.
rewrite cap_universal cap_universal.
apply inc_refl.
Qed.

(** %
\begin{screen}
\begin{lemma}[function\_dedekind1, function\_dedekind2]
Let $f:A \to B$ be a function, $\mu :C \rel A$ and $\rho :C \rel B$. Then,
$$
(\mu \sqcap \rho \cdot f^\sharp) \cdot f = \mu \cdot f \sqcap \rho \land \rho \cdot f^\sharp \cdot f = \nabla_{CA} \cdot f \sqcap \rho.
$$
\end{lemma}
\end{screen}
% **)
Lemma function_dedekind1
 {A B C : eqType} {f : Rel A B} {mu : Rel C A} {rho : Rel C B}:
 function_r f -> (mu ∩ (rho ・ f #)) ・ f = (mu ・ f) ∩ rho.
Proof.
move => H.
apply inc_antisym.
apply (@inc_trans _ _ _ _ _ (comp_cap_distr_r)).
apply cap_inc_compat_l.
rewrite comp_assoc.
apply comp_inc_compat_ab_a.
apply H.
apply (@inc_trans _ _ _ _ _ (@dedekind _ _ _ _ _ _)).
apply comp_inc_compat_ab_ab'.
apply cap_l.
Qed.

Lemma function_dedekind2 {A B C : eqType} {f : Rel A B} {rho : Rel C B}:
 function_r f -> (rho ・ f #) ・ f = (∇ C A ・ f) ∩ rho.
Proof.
move => H.
move : (@function_dedekind1 _ _ _ f (∇ C A) rho H) => H0.
rewrite cap_comm cap_universal in H0.
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

(** %
\section{全射, 単射に関する補題}
\begin{screen}
\begin{lemma}[surjection\_comp]
Let $\alpha :A \rel B$ and $\beta :B \rel C$ be surjections, then $\alpha \cdot \beta$ is also a surjection.
\end{lemma}
\end{screen}
% **)
Lemma surjection_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 surjection_r alpha -> surjection_r beta -> surjection_r (alpha ・ beta).
Proof.
rewrite /surjection_r.
elim => H H0.
elim => H1 H2.
split.
apply (function_comp H H1).
rewrite comp_inv.
apply (total_comp H2 H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[injection\_comp]
Let $\alpha :A \rel B$ and $\beta :B \rel C$ be injections, then $\alpha \cdot \beta$ is also an injection.
\end{lemma}
\end{screen}
% **)
Lemma injection_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 injection_r alpha -> injection_r beta -> injection_r (alpha ・ beta).
Proof.
rewrite /injection_r.
elim => H H0.
elim => H1 H2.
split.
apply (function_comp H H1).
rewrite comp_inv.
apply (univalent_comp H2 H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[bijection\_comp]
Let $\alpha :A \rel B$ and $\beta :B \rel C$ be bijections, then $\alpha \cdot \beta$ is also a bijection.
\end{lemma}
\end{screen}
% **)
Lemma bijection_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 bijection_r alpha -> bijection_r beta -> bijection_r (alpha ・ beta).
Proof.
rewrite /bijection_r.
elim => H.
elim => H0 H1.
elim => H2.
elim => H3 H4.
split.
apply (function_comp H H2).
rewrite comp_inv.
split.
apply (total_comp H3 H0).
apply (univalent_comp H4 H1).
Qed.

(** %
\begin{screen}
\begin{lemma}[surjection\_unique1]
Let $e:A \twoheadrightarrow B$ be a surjection, $f:A \to C$ be a function and $e \cdot e^\sharp \sqsubseteq f \cdot f^\sharp$, then there exists a unique function $g:B \to C$ s.t. $f=eg$.
\end{lemma}
\end{screen}
% **)
Lemma surjection_unique1 {A B C : eqType} {e : Rel A B} {f : Rel A C}:
 surjection_r e -> function_r f -> (e ・ e #) ⊆ (f ・ f #) ->
 (exists! g : Rel B C, function_r g /\ f = e ・ g).
Proof.
rewrite /surjection_r/function_r/total_r/univalent_r.
elim.
elim => H H0 H1.
elim => H2 H3 H4.
exists (e # ・ f).
repeat split.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ f).
apply (@inc_trans _ _ _ _ _ H1).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_b_ab.
apply H2.
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ e).
apply (@inc_trans _ _ _ (f # ・ ((f ・ f #) ・ f))).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_a'b H4).
rewrite comp_assoc -comp_assoc.
apply (fun H' => @inc_trans _ _ _ _ _ H' H3).
apply (comp_inc_compat_ab_a H3).
apply function_inc.
split.
apply H2.
apply H3.
split.
rewrite /total_r.
rewrite comp_inv comp_inv inv_invol.
rewrite -(@comp_assoc _ _ _ _ e) (@comp_assoc _ _ _ _ _ e) (@comp_assoc _ _ _ _ _ f) -(@comp_assoc _ _ _ _ f).
apply (@inc_trans _ _ _ _ _ H).
apply comp_inc_compat_a_ab.
apply (@inc_trans _ _ _ _ _ H2).
apply (comp_inc_compat_a_ab H).
rewrite /univalent_r.
rewrite comp_inv comp_inv inv_invol.
rewrite (@comp_assoc _ _ _ _ _ e) -(@comp_assoc _ _ _ _ e) comp_assoc -(@comp_assoc _ _ _ _ _ _ f).
apply (@inc_trans _ _ _ (f # ・ (((f ・ f #) ・ (f ・ f #)) ・ f))).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_ab_a'b.
apply comp_inc_compat.
apply H4.
apply H4.
rewrite comp_assoc (@comp_assoc _ _ _ _ _ _ f) -(@comp_assoc _ _ _ _ (f #)) -(@comp_assoc _ _ _ _ (f #)) (@comp_assoc _ _ _ _ _ (f #)) -(@comp_assoc _ _ _ _ (f #)).
apply (fun H' => @inc_trans _ _ _ _ _ H' H3).
apply comp_inc_compat_ab_a.
apply (fun H' => @inc_trans _ _ _ _ _ H' H3).
apply (comp_inc_compat_ab_a H3).
rewrite -comp_assoc.
apply (comp_inc_compat_b_ab H).
move => g.
elim.
elim => H5 H6 H7.
replace g with (e # ・ (e ・ g)).
apply f_equal.
apply H7.
rewrite -comp_assoc.
apply inc_antisym.
apply (comp_inc_compat_ab_b H0).
rewrite inv_invol in H1.
apply (comp_inc_compat_b_ab H1).
Qed.

(** %
\begin{screen}
\begin{lemma}[surjection\_unique2]
Let $e:A \twoheadrightarrow B$ be a surjection, $f:A \to C$ be a function and $e \cdot e^\sharp = f \cdot f^\sharp$, then function $e^\sharp f$ is an injection.
\end{lemma}
\end{screen}
% **)
Lemma surjection_unique2 {A B C : eqType} {e : Rel A B} {f : Rel A C}:
 surjection_r e -> function_r f -> (e ・ e #) = (f ・ f #) -> injection_r (e # ・ f).
Proof.
rewrite /surjection_r/injection_r/function_r/total_r/univalent_r.
elim.
elim => H H0 H1.
elim => H2 H3 H4.
repeat split.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ f).
apply (@inc_trans _ _ _ _ _ H1).
apply comp_inc_compat_ab_ab'.
apply comp_inc_compat_b_ab.
apply H2.
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ e).
rewrite H4.
rewrite comp_assoc -comp_assoc.
apply (fun H' => @inc_trans _ _ _ _ _ H' H3).
apply (comp_inc_compat_ab_a H3).
rewrite inv_invol comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ f).
rewrite -H4.
rewrite comp_assoc -comp_assoc.
apply (fun H' => @inc_trans _ _ _ _ _ H' H0).
apply comp_inc_compat_ab_a.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[injection\_unique1]
Let $m:B \rightarrowtail A$ be an injection, $f:C \to A$ be a function and $f^\sharp \cdot f \sqsubseteq m^\sharp \cdot m$, then there exists a unique function $g:C \to B$ s.t. $f=gm$.
\end{lemma}
\end{screen}
% **)
Lemma injection_unique1 {A B C : eqType} {m : Rel B A} {f : Rel C A}:
 injection_r m -> function_r f -> (f # ・ f) ⊆ (m # ・ m) ->
 (exists! g : Rel C B, function_r g /\ f = g ・ m).
Proof.
rewrite /injection_r/function_r/total_r/univalent_r.
elim.
elim => H H0 H1.
elim => H2 H3 H4.
exists (f ・ m #).
repeat split.
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ _ m).
apply (@inc_trans _ _ _ (f ・ ((f # ・ f) ・ f #))).
rewrite comp_assoc -comp_assoc.
apply (@inc_trans _ _ _ _ _ H2).
apply (comp_inc_compat_a_ab H2).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_a'b H4).
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ f).
apply (fun H' => @inc_trans _ _ _ _ _ H' H1).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H3).
rewrite comp_assoc.
apply Logic.eq_sym.
apply function_inc.
split.
rewrite /total_r.
rewrite comp_inv comp_inv inv_invol.
apply (@inc_trans _ _ _ _ _ H2).
apply comp_inc_compat.
apply (@inc_trans _ _ _ (f ・ (f # ・ f))).
rewrite -comp_assoc.
apply (comp_inc_compat_b_ab H2).
apply (comp_inc_compat_ab_ab' H4).
apply (@inc_trans _ _ _ ((f # ・ f) ・ f #)).
rewrite comp_assoc.
apply (comp_inc_compat_a_ab H2).
apply (comp_inc_compat_ab_a'b H4).
rewrite /univalent_r.
rewrite comp_inv comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ _ f).
apply (fun H' => @inc_trans _ _ _ _ _ H' H0).
apply comp_inc_compat_ab_a.
apply (fun H' => @inc_trans _ _ _ _ _ H' H3).
apply (comp_inc_compat_ab_a H0).
split.
apply H2.
apply H3.
apply (comp_inc_compat_ab_a H0).
move => g.
elim.
elim => H5 H6 H7.
rewrite H7 comp_assoc.
apply inc_antisym.
rewrite inv_invol in H1.
apply (comp_inc_compat_ab_a H1).
apply (comp_inc_compat_a_ab H).
Qed.

(** %
\begin{screen}
\begin{lemma}[injection\_unique2]
Let $m:B \rightarrowtail A$ be an injection, $f:C \to A$ be a function and $f^\sharp \cdot f = m^\sharp \cdot m$, then function $f \cdot m^\sharp$ is a surjection.
\end{lemma}
\end{screen}
% **)
Lemma injection_unique2 {A B C : eqType} {m : Rel B A} {f : Rel C A}:
 injection_r m -> function_r f -> (f # ・ f) = (m # ・ m) -> surjection_r (f ・ m #).
Proof.
rewrite /surjection_r/injection_r/function_r/total_r/univalent_r.
elim.
elim => H H0 H1.
elim => H2 H3 H4.
repeat split.
rewrite comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ _ m).
apply (@inc_trans _ _ _ (f ・ ((f # ・ f) ・ f #))).
rewrite comp_assoc -comp_assoc.
apply (@inc_trans _ _ _ _ _ H2).
apply (comp_inc_compat_a_ab H2).
apply comp_inc_compat_ab_ab'.
rewrite H4.
apply inc_refl.
rewrite comp_inv comp_assoc -(@comp_assoc _ _ _ _ _ f).
apply (fun H' => @inc_trans _ _ _ _ _ H' H1).
apply comp_inc_compat_ab_ab'.
apply (comp_inc_compat_ab_b H3).
rewrite inv_invol comp_inv inv_invol comp_assoc -(@comp_assoc _ _ _ _ _ f).
apply (@inc_trans _ _ _ _ _ H).
apply comp_inc_compat_ab_ab'.
rewrite H4 comp_assoc.
apply (comp_inc_compat_a_ab H).
Qed.

(** %
\begin{screen}
\begin{lemma}[bijection\_inv]
Let $\alpha :A \rel B$, $\beta :B \rel A$, $\alpha \cdot \beta = id_A$ and $\beta \cdot \alpha = id_B$, then $\alpha$ and $\beta$ are bijections and $\beta = \alpha^\sharp$.
\end{lemma}
\end{screen}
% **)
Lemma bijection_inv {A B : eqType} {alpha : Rel A B} {beta : Rel B A}:
 alpha ・ beta = Id A -> beta ・ alpha = Id B -> bijection_r alpha /\ bijection_r beta /\ beta = alpha #.
Proof.
move => H H0.
move : (@id_function A) => H1.
move : (@id_function B) => H2.
assert (bijection_r alpha /\ bijection_r beta).
assert (total_r alpha /\ total_r (alpha #) /\ total_r beta /\ total_r (beta #)).
repeat split.
apply (@total_comp2 _ _ _ _ beta).
rewrite H.
apply H1.
apply (@total_comp2 _ _ _ _ (beta #)).
rewrite -comp_inv H0 inv_id.
apply H2.
apply (@total_comp2 _ _ _ _ alpha).
rewrite H0.
apply H2.
apply (@total_comp2 _ _ _ _ (alpha #)).
rewrite -comp_inv H inv_id.
apply H1.
repeat split.
apply H3.
apply (@univalent_comp2 _ _ _ beta).
rewrite H0.
apply H2.
apply H3.
apply H3.
apply (@univalent_comp2 _ _ _ (beta #)).
rewrite -comp_inv H inv_id.
apply H1.
rewrite inv_invol.
apply H3.
apply H3.
apply (@univalent_comp2 _ _ _ alpha).
rewrite H.
apply H1.
apply H3.
apply H3.
apply (@univalent_comp2 _ _ _ (alpha #)).
rewrite -comp_inv H0 inv_id.
apply H2.
rewrite inv_invol.
apply H3.
split.
apply H3.
split.
apply H3.
rewrite -(@comp_id_r _ _ beta) -(@comp_id_l _ _ (alpha #)).
rewrite -H0 comp_assoc.
apply f_equal.
apply inc_antisym.
apply H3.
rewrite comp_inv_inv -inv_inc_move inv_id.
apply H3.
Qed.

(** %
\begin{screen}
\begin{lemma}[bijection\_inv\_corollary]
Let $\alpha :A \rel B$ be a bijection, then $\alpha^\sharp$ is also a bijection.
\end{lemma}
\end{screen}
% **)
Lemma bijection_inv_corollary {A B : eqType} {alpha : Rel A B}:
 bijection_r alpha -> bijection_r (alpha #).
Proof.
move : (@bijection_inv _ _ alpha (alpha #)) => H.
move => H0.
rewrite /bijection_r/function_r/total_r/univalent_r in H0.
rewrite inv_invol in H0.
apply H.
apply inc_antisym.
apply H0.
apply H0.
apply inc_antisym.
apply H0.
apply H0.
Qed.

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