Require Export ssreflect eqtype bigop.
Require Export Logic.ClassicalFacts.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.Classical_Prop.
Require Import Logic.IndefiniteDescription.
Require Import Logic.ProofIrrelevance.

Axiom prop_extensionality_ok : prop_extensionality.

(** %
\section{定義}
この章では, 関係を集合論的に定義した場合の定義, およびその定義で諸公理が成立することを示す. 公理名や記号などは \verb|Basic_Notations| と同じものを使用するため, \verb|Basic_Lemms| 以降ではそれの代わりにこのライブラリをインポートすることもできる.
% **)

Definition Rel (A B : eqType) := A -> B -> Prop.

Definition inverse {A B : eqType} (alpha : Rel A B) : Rel B A
 := (fun (b : B)(a : A) => alpha a b).
Notation "a #" := (inverse a) (at level 20).
Definition composite {A B C : eqType} (alpha : Rel A B) (beta : Rel B C) : Rel A C
 := (fun (a : A)(c : C) => exists b : B, alpha a b /\ beta b c).
Notation "a '・' b" := (composite a b) (at level 50).
Definition residual {A B C : eqType} (alpha : Rel A B) (beta : Rel B C) : Rel A C
 := (fun (a : A)(c : C) => forall b : B, alpha a b -> beta b c).
Notation "a '△' b" := (residual a b) (at level 50).

Definition identity (A : eqType) : Rel A A := (fun a a0 : A => a = a0).
Notation "'Id'" := identity.
Definition empty (A B : eqType) : Rel A B := (fun (a : A)(b : B) => False).
Notation "'φ'" := empty.
Definition universal (A B : eqType) : Rel A B := (fun (a : A)(b : B) => True).
Notation "'∇'" := universal.

Definition include {A B : eqType} (alpha beta : Rel A B) : Prop
 := (forall (a : A)(b : B), alpha a b -> beta a b).
Notation "a '⊆' b" := (include a b) (at level 50).

Definition cup {A B : eqType} (alpha beta : Rel A B) : Rel A B
 := (fun (a : A)(b : B) => alpha a b \/ beta a b).
Notation "a '∪' b" := (cup a b) (at level 50).
Definition cap {A B : eqType} (alpha beta : Rel A B) : Rel A B
 := (fun (a : A)(b : B) => alpha a b /\ beta a b).
Notation "a '∩' b" := (cap a b) (at level 50).
Definition rpc {A B : eqType} (alpha beta : Rel A B) : Rel A B
 := (fun (a : A)(b : B) => alpha a b -> beta a b).
Notation "a '>>' b" := (rpc a b) (at level 50).
Definition complement {A B : eqType} (alpha : Rel A B) := alpha >> φ A B.
Notation "a '^'" := (complement a) (at level 20).
Definition difference {A B : eqType} (alpha beta : Rel A B) := alpha ∩ beta ^.
Notation "a -- b" := (difference a b) (at level 50).

Definition capP {A B L : eqType} (P : L -> Prop) (alpha_L : L -> Rel A B) : Rel A B
 := (fun (a : A)(b : B) => forall l : L, P l -> alpha_L l a b).
Notation "'∩_{' p '}'  a" := (capP p a) (at level 50).
Definition cupP {A B L : eqType} (P : L -> Prop) (alpha_L : L -> Rel A B) : Rel A B
 := (fun (a : A)(b : B) => exists l : L, P l /\ alpha_L l a b).
Notation "'∪_{' p '}'  a" := (cupP p a) (at level 50).

Notation "'i'" := unit_eqType.

(** %
\section{関数の定義}
% **)
Definition total_r {A B : eqType} (alpha : Rel A B) := (Id A) ⊆ (alpha ・ alpha #).
Definition univalent_r {A B : eqType} (alpha : Rel A B) := (alpha # ・ alpha) ⊆ (Id B).
Definition function_r {A B : eqType} (alpha : Rel A B)
 := (total_r alpha) /\ (univalent_r alpha).
Definition surjection_r {A B : eqType} (alpha : Rel A B)
 := (function_r alpha) /\ (total_r (alpha #)).
Definition injection_r {A B : eqType} (alpha : Rel A B)
 := (function_r alpha) /\ (univalent_r (alpha #)).
Definition bijection_r {A B : eqType} (alpha : Rel A B)
 := (function_r alpha) /\ (total_r (alpha #)) /\ (univalent_r (alpha #)).

(** %
\section{関係の公理}
今後の諸定理の証明は, 原則以下の公理群, およびそれらから導かれる補題のみを用いて行っていくことにする.
% **)

(** %
\subsection{Dedekind 圏の公理}
\begin{screen}
\begin{lemma}[comp\_id\_l, comp\_id\_r]
Let $\alpha :A \rel B$. Then,
$$
id_A \cdot \alpha = \alpha \cdot id_B = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom1a := forall (A B : eqType)(alpha : Rel A B), Id A ・ alpha = alpha.
Lemma comp_id_l : axiom1a.
Proof.
move => A B alpha.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split.
elim => a0.
elim => H H0.
rewrite H.
apply H0.
move => H.
exists a.
split.
by [].
apply H.
Qed.

Definition axiom1b :=  forall (A B : eqType)(alpha : Rel A B), alpha ・ Id B = alpha.
Lemma comp_id_r : axiom1b.
Proof.
move => A B alpha.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split.
elim => b0.
elim => H H0.
rewrite -H0.
apply H.
move => H.
exists b.
split.
apply H.
by [].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_assoc]
Let $\alpha :A \rel B$, $\beta :B \rel C$, and $\gamma :C \rel D$. Then,
$$
(\alpha \cdot \beta) \cdot \gamma = \alpha \cdot (\beta \cdot \gamma).
$$
\end{lemma}
\end{screen}
% **)
Definition axiom2 :=
 forall (A B C D : eqType)(alpha : Rel A B)(beta : Rel B C)(gamma : Rel C D),
 (alpha ・ beta) ・ gamma = alpha ・ (beta ・ gamma).
Lemma comp_assoc : axiom2.
Proof.
move => A B C D alpha beta gamma.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => d.
apply prop_extensionality_ok.
split.
elim => c.
elim => H H0.
elim H => b H1.
exists b.
split.
apply H1.
exists c.
split.
apply H1.
apply H0.
elim => b.
elim => H.
elim => c H0.
exists c.
split.
exists b.
split.
apply H.
apply H0.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_refl]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom3 := forall (A B : eqType)(alpha : Rel A B), alpha ⊆ alpha.
Lemma inc_refl : axiom3.
Proof.
by [rewrite /axiom3/include].
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_trans]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \land \beta \sqsubseteq \gamma \Rightarrow \alpha \sqsubseteq \gamma.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom4 := forall (A B : eqType)(alpha beta gamma : Rel A B),
 alpha ⊆ beta -> beta ⊆ gamma -> alpha ⊆ gamma.
Lemma inc_trans : axiom4.
Proof.
move => A B alpha beta gamma H H0 a b H1.
apply (H0 _ _ (H _ _ H1)).
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_antisym]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \land \beta \sqsubseteq \alpha \Rightarrow \alpha = \beta.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom5 := forall (A B : eqType)(alpha beta : Rel A B),
 alpha ⊆ beta -> beta ⊆ alpha -> alpha = beta.
Lemma inc_antisym : axiom5.
Proof.
move => A B alpha beta H H0.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split.
apply H.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_empty\_alpha]
Let $\alpha :A \rel B$. Then,
$$
\phi_{AB} \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom6 := forall (A B : eqType)(alpha : Rel A B), φ A B ⊆ alpha.
Lemma inc_empty_alpha : axiom6.
Proof.
move => A B alpha a b.
apply False_ind.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_alpha\_universal]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqsubseteq \nabla_{AB}.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom7 := forall (A B : eqType)(alpha : Rel A B), alpha ⊆ ∇ A B.
Lemma inc_alpha_universal : axiom7.
Proof.
move => A B alpha a b H.
apply I.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_cap]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq (\beta \sqcap \gamma) \Leftrightarrow \alpha \sqsubseteq \beta \land \alpha \sqsubseteq \gamma.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom8 := forall (A B : eqType)(alpha beta gamma : Rel A B),
 alpha ⊆ (beta ∩ gamma) <-> (alpha ⊆ beta) /\ (alpha ⊆ gamma).
Lemma inc_cap : axiom8.
Proof.
move => A B alpha beta gamma.
split; move => H.
split.
move => a b H0.
apply (H a b H0).
move => a b H0.
apply (H a b H0).
move => a b H0.
split.
apply H.
apply H0.
apply H.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_cup]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\beta \sqcup \gamma) \sqsubseteq \alpha \Leftrightarrow \beta \sqsubseteq \alpha \land \gamma \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom9 := forall (A B : eqType)(alpha beta gamma : Rel A B),
 (beta ∪ gamma) ⊆ alpha <-> (beta ⊆ alpha) /\ (gamma ⊆ alpha).
Lemma inc_cup : axiom9.
Proof.
move => A B alpha beta gamma.
split; move => H.
split.
move => a b H0.
apply H.
left.
apply H0.
move => a b H0.
apply H.
right.
apply H0.
move => a b.
case; apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_capP]
Let $\alpha , \beta_\lambda :A \rel B$ and $P$ : predicate. Then,
$$
\alpha \sqsubseteq (\sqcap_{P(\lambda)} \beta_\lambda) \Leftrightarrow \forall \lambda \in \Lambda , P(\lambda) \Rightarrow \alpha \sqsubseteq \beta_\lambda.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom10 :=
 forall (A B L : eqType)(alpha : Rel A B)(beta_L : L -> Rel A B)(P : L -> Prop),
 alpha ⊆ (∩_{P} beta_L) <-> forall l : L, P l -> alpha ⊆ beta_L l.
Lemma inc_capP : axiom10.
Proof.
move => A B L alpha beta_L P.
split; move => H.
move => l H0 a b H1.
apply (H _ _ H1 _ H0).
move => a b H0 l H1.
apply (H _ H1 _ _ H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_cupP]
Let $\alpha , \beta_\lambda :A \rel B$. Then,
$$
(\sqcup_{P(\lambda)} \beta_\lambda) \sqsubseteq \alpha \Leftrightarrow \forall \lambda \in \Lambda , P(\lambda) \Rightarrow \beta_\lambda \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom11 :=
 forall (A B L : eqType)(alpha : Rel A B)(beta_L : L -> Rel A B)(P : L -> Prop),
 (∪_{P} beta_L) ⊆ alpha <-> forall l : L, P l -> beta_L l ⊆ alpha.
Lemma inc_cupP : axiom11.
Proof.
move => A B L alpha beta_L P.
split.
move => H l H0 a b H1.
apply H.
exists l.
split.
apply H0.
apply H1.
move => H a b.
elim => l.
elim => H0 H1.
apply (H l H0 _ _ H1).
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_rpc]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq (\beta \Rightarrow \gamma) \Leftrightarrow (\alpha \sqcap \beta) \sqsubseteq \gamma.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom12 := forall (A B : eqType)(alpha beta gamma : Rel A B),
 alpha ⊆ (beta >> gamma) <-> (alpha ∩ beta) ⊆ gamma.
Lemma inc_rpc : axiom12.
Proof.
move => A B alpha beta gamma.
split; move => H.
move => a b.
elim => H0 H1.
apply (H _ _ H0 H1).
move => a b H0 H1.
apply H.
split.
apply H0.
apply H1.
Qed.

(** %
\begin{screen}
\begin{lemma}[inv\_invol]
Let $\alpha :A \rel B$. Then,
$$
(\alpha^\sharp)^\sharp = \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom13 := forall (A B : eqType)(alpha : Rel A B), (alpha #) # = alpha.
Lemma inv_invol : axiom13.
Proof.
by [move => A B alpha].
Qed.

(** %
\begin{screen}
\begin{lemma}[comp\_inv]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
(\alpha \cdot \beta)^\sharp = \beta^\sharp \cdot \alpha^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom14 := forall (A B C : eqType)(alpha : Rel A B)(beta : Rel B C),
 (alpha ・ beta) # = (beta # ・ alpha #).
Lemma comp_inv : axiom14.
Proof.
move => A B C alpha beta.
apply functional_extensionality.
move => c.
apply functional_extensionality.
move => a.
apply prop_extensionality_ok.
split; elim => b.
elim => H H0.
exists b.
split.
apply H0.
apply H.
elim => H H0.
exists b.
split.
apply H0.
apply H.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_inv]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \Rightarrow \alpha^\sharp \sqsubseteq \beta^\sharp.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom15 :=
 forall (A B : eqType)(alpha beta : Rel A B), alpha ⊆ beta -> alpha # ⊆ beta #.
Lemma inc_inv : axiom15.
Proof.
move => A B alpha beta H b a H0.
apply (H _ _ H0).
Qed.

(** %
\begin{screen}
\begin{lemma}[dedekind]
Let $\alpha :A \rel B$, $\beta :B \rel C$, and $\gamma :A \rel C$. Then,
$$
(\alpha \cdot \beta) \sqcap \gamma \sqsubseteq (\alpha \sqcap (\gamma \cdot \beta^\sharp)) \cdot (\beta \sqcap (\alpha^\sharp \cdot \gamma)).
$$
\end{lemma}
\end{screen}
% **)
Definition axiom16 :=
 forall (A B C : eqType)(alpha : Rel A B)(beta : Rel B C)(gamma : Rel A C),
 ((alpha ・ beta) ∩ gamma)
 ⊆ ((alpha ∩ (gamma ・ beta #)) ・ (beta ∩ (alpha # ・ gamma))).
Lemma dedekind : axiom16.
Proof.
move => A B C alpha beta gamma a c.
elim.
elim => b.
move => H H0.
exists b.
repeat split.
apply H.
exists c.
split.
apply H0.
apply H.
apply H.
exists a.
split.
apply H.
apply H0.
Qed.

(** %
\begin{screen}
\begin{lemma}[inc\_residual]
Let $\alpha :A \rel B$, $\beta :B \rel C$, and $\gamma :A \rel C$. Then,
$$
\gamma \sqsubseteq (\alpha \rhd \beta) \Leftrightarrow \alpha^\sharp \cdot \gamma \sqsubseteq \beta.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom17 :=
 forall (A B C : eqType)(alpha : Rel A B)(beta : Rel B C)(gamma : Rel A C),
 gamma ⊆ (alpha △ beta) <-> (alpha # ・ gamma) ⊆ beta.
Lemma inc_residual : axiom17.
Proof.
move => A B C alpha beta gamma.
split; move => H.
move => b c.
elim => a H0.
apply (H a).
apply H0.
apply H0.
move => a c H0 b H1.
apply H.
exists a.
split.
apply H1.
apply H0.
Qed.

(** %
\subsection{排中律}
\begin{screen}
Dedekind 圏の公理のほかに, 以下の ``排中律'' を仮定すれば, 与えられる圏は Schr$\ddot{\mbox{o}}$der 圏となり, Bool 代数の性質も満たされる. ちなみに剰余合成は補関係から定義可能なので, 本来 Schr$\ddot{\mbox{o}}$der 圏には剰余合成に関する公理は存在しない.
\begin{lemma}[complement\_classic]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcup \alpha^- = \nabla_{AB}
$$
\end{lemma}
\end{screen}
% **)
Definition axiom18 := forall (A B : eqType)(alpha : Rel A B),
 alpha ∪ alpha ^ = ∇ A B.
Lemma complement_classic : axiom18.
Proof.
move => A B alpha.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split; move => H.
apply I.
apply classic.
Qed.

(** %
\subsection{単域}
\begin{screen}
1 点集合 $I$ が単域となるための条件は
$$
\phi_{II} \neq id_I \land id_I = \nabla_{II} \land \forall X, \nabla_{XI} \cdot \nabla_{IX} = \nabla_{XX}
$$
だが, Rel の定義から左 2 つは証明できるため, 右の式だけ仮定する.
\begin{lemma}[unit\_universal]
$$
\nabla_{AI} \cdot \nabla_{IA} = \nabla_{AA}
$$
\end{lemma}
\end{screen}
% **)
Definition axiom19 := forall (A : eqType), ∇ A i ・ ∇ i A = ∇ A A.
Lemma unit_universal : axiom19.
Proof.
move => A.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => a0.
apply prop_extensionality_ok.
split; move => H.
apply I.
exists tt.
by [].
Qed.

(** %
\subsection{点公理}
\begin{screen}
この ``弱選択公理'' を仮定すれば, 排中律と単域の存在(厳密には全域性公理)を利用して点公理を導出できる.
\begin{lemma}[weak\_axiom\_of\_choice]
Let $\alpha :I \rel A$ be a total relation. Then,
$$
\exists \beta :I \to A, \beta \sqsubseteq \alpha.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom20 := forall (A : eqType)(alpha : Rel i A),
 total_r alpha -> exists beta : Rel i A, function_r beta /\ beta ⊆ alpha.
Lemma weak_axiom_of_choice : axiom20.
Proof.
move => A alpha.
rewrite /function_r/total_r/univalent_r/identity/include/composite/inverse.
move => H.
move : (H tt tt (Logic.eq_refl tt)).
elim => a H0.
exists (fun (_ : i)(a0 : A) => a = a0).
repeat split.
move => tt tt0 H1.
by [exists a].
move => a0 a1.
elim => tt0.
elim => H1 H2.
by [rewrite -H1 -H2].
induction a0.
move => a0 H1.
rewrite -H1.
apply H0.
Qed.

(** %
\subsection{関係の有理性}
\begin{screen}
集合の選択公理(\verb|Logic.IndefiniteDescription|)や証明の一意性 \\
(\verb|Logic.ProofIrrelevance|)を仮定すれば, 集合論上ならごり押しで証明できる. \\
旧ライブラリの頃は無理だと諦めて Axiom を追加していたが, Standard Library のインポートだけで解けた. 正直びっくり.
\begin{lemma}[rationality]
Let $\alpha :A \rel B$. Then,
$$
\exists R, \exists f:R \to A, \exists g:R \to B, \alpha = f^\sharp \cdot g \land f \cdot f^\sharp \sqcap g \cdot g^\sharp = id_R.
$$
\end{lemma}
\end{screen}
% **)

(** %
\hrulefill \\
この付近は, ごり押しのための補題. 命題の真偽を選択公理で bool 値に変換したり, 部分集合の元から上位集合の元を生成する \verb|sval| (\verb|proj1_sig|) の単射性を示したりしている.
% **)

Lemma is_true_inv0 : forall P : Prop, exists b : bool, P <-> is_true b.
Proof.
move => P.
case (classic P); move => H.
exists true.
split; move => H0.
by [].
apply H.
exists false.
split; move => H0.
apply False_ind.
apply (H H0).
discriminate H0.
Qed.
Definition is_true_inv : Prop -> bool.
move => P.
move : (is_true_inv0 P) => H.
apply constructive_indefinite_description in H.
apply H.
Defined.
Lemma is_true_id : forall P : Prop, is_true (is_true_inv P) <-> P.
Proof.
move => P.
unfold is_true_inv.
move : (constructive_indefinite_description (fun b : bool => P <-> is_true b) (is_true_inv0 P)) => x0.
apply (@sig_ind bool (fun b => (P <-> is_true b)) (fun y => is_true (let (x, _) := y in x) <-> P)).
move => x H.
apply iff_sym.
apply H.
Qed.
Lemma sval_inv : forall (A : Type)(P : A -> Prop)(x : sig P)(a : A), a = sval x -> exists (H : P a), x = exist P a H.
Proof.
move => A P x a H0.
rewrite H0.
exists (proj2_sig x).
apply (@sig_ind A P (fun y => y = exist P (sval y) (proj2_sig y))).
move => a0 H.
by [simpl].
Qed.
Lemma sval_injective : forall (A : Type)(P : A -> Prop)(x y : sig P), sval x = sval y -> x = y.
Proof.
move => A P x y H.
move : (sval_inv A P y (sval x) H).
elim => H0 H1.
rewrite H1.
assert (H0 = proj2_sig x).
apply proof_irrelevance.
rewrite H2.
apply (@sig_ind A P (fun y => y = exist P (sval y) (proj2_sig y))).
move => a0 H3.
by [simpl].
Qed.
(** %
\hrulefill
% **)

Definition axiom21 := forall (A B : eqType)(alpha : Rel A B),
 exists (R : eqType)(f : Rel R A)(g : Rel R B),
 function_r f /\ function_r g /\ alpha = f # ・ g /\ ((f ・ f #) ∩ (g ・ g #)) = Id R.
Lemma rationality : axiom21.
Proof.
move => A B alpha.
rewrite /function_r/total_r/univalent_r/identity/cap/composite/inverse/include.
exists (sig_eqType (fun x : prod_eqType A B => is_true_inv (alpha (fst x) (snd x)))).
exists (fun x a => a = (fst (sval x))).
exists (fun x b => b = (snd (sval x))).
simpl.
repeat split.
move => x x0 H.
exists (fst (sval x)).
repeat split.
by [rewrite H].
move => a a0.
elim => x.
elim => H H0.
by [rewrite H H0].
move => x x0 H.
exists (snd (sval x)).
repeat split.
by [rewrite H].
move => b b0.
elim => x.
elim => H H0.
by [rewrite H H0].
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split; move => H.
assert (is_true (is_true_inv (alpha (fst (a,b)) (snd (a,b))))).
simpl.
apply is_true_id.
apply H.
exists (exist (fun x => (is_true (is_true_inv (alpha (fst x) (snd x))))) (a,b) H0).
by [simpl].
elim H => x.
elim => H0 H1.
rewrite H0 H1.
apply is_true_id.
apply (@sig_ind (A * B) (fun x => is_true (is_true_inv (alpha (fst x) (snd x)))) (fun x => is_true (is_true_inv (alpha (fst (sval x)) (snd (sval x)))))).
simpl.
by [move => x0].
apply functional_extensionality.
move => y.
apply functional_extensionality.
move => y0.
apply prop_extensionality_ok.
split; move => H.
apply sval_injective.
elim H => H0 H1.
elim H0 => a.
elim => H2 H3.
elim H1 => b.
elim => H4 H5.
rewrite (surjective_pairing (sval y0)) -H3 -H5 H2 H4.
apply surjective_pairing.
rewrite H.
split.
exists (fst (sval y0)).
repeat split.
exists (snd (sval y0)).
repeat split.
Qed.

(** %
\subsection{直和と直積}
\begin{screen}
任意の直和に対して, 入射対が存在することを仮定する.
\begin{lemma}[pair\_of\_inclusions]
$\exists j:A \to A+B, \exists k:B \to A+B,$
$$
j \cdot j^\sharp = id_A \land k \cdot k^\sharp = id_B \land j \cdot k^\sharp = \phi_{AB} \land j^\sharp \cdot j \sqcup k^\sharp \cdot k = id_{A+B}.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom22 :=
 forall (A B : eqType), exists (j : Rel A (sum_eqType A B))(k : Rel B (sum_eqType A B)),
 j ・ j # = Id A /\ k ・ k # = Id B /\ j ・ k # = φ A B /\
 (j # ・ j) ∪ (k # ・ k) = Id (sum_eqType A B).
Lemma pair_of_inclusions : axiom22.
Proof.
move => A B.
exists (fun (a : A)(x : sum_eqType A B) => x = inl a).
exists (fun (b : B)(x : sum_eqType A B) => x = inr b).
repeat split.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => a0.
apply prop_extensionality_ok.
split; move => H.
elim H => x.
elim => H0 H1.
rewrite H0 in H1.
by [injection H1].
exists (inl a).
repeat split.
by [rewrite H].
apply functional_extensionality.
move => b.
apply functional_extensionality.
move => b0.
apply prop_extensionality_ok.
split; move => H.
elim H => x.
elim => H0 H1.
rewrite H0 in H1.
by [injection H1].
exists (inr b).
repeat split.
by [rewrite H].
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split; move => H.
elim H => x.
elim => H0 H1.
rewrite H0 in H1.
discriminate H1.
apply False_ind.
apply H.
apply functional_extensionality.
move => x.
apply functional_extensionality.
move => x0.
apply prop_extensionality_ok.
split.
case.
elim => a.
elim => H0 H1.
by [rewrite H0 H1].
elim => b.
elim => H0 H1.
by [rewrite H0 H1].
move : x0.
apply (sum_ind (fun x0 => x = x0 -> (exists b : A, x = inl b /\ x0 = inl b) \/ (exists b : B, x = inr b /\ x0 = inr b))).
move => a H.
left.
exists a.
repeat split.
apply H.
move => b H.
right.
exists b.
repeat split.
apply H.
Qed.

(** %
\begin{screen}
任意の直積に対して, 射影対が存在することを仮定する.
\begin{lemma}[pair\_of\_projections]
$\exists p:A \times B \to A, \exists q:A \times B \to B,$
$$
p^\sharp \cdot q = \nabla_{AB} \land p \cdot p^\sharp \sqcap q \cdot q^\sharp = id_{A \times B}.
$$
\end{lemma}
\end{screen}
% **)
Definition axiom23 :=
 forall (A B : eqType), exists (p : Rel (prod_eqType A B) A)(q : Rel (prod_eqType A B) B),
 p # ・ q = ∇ A B /\ (p ・ p #) ∩ (q ・ q #) = Id (prod_eqType A B) /\ univalent_r p /\ univalent_r q.
Lemma pair_of_projections : axiom23.
Proof.
move => A B.
exists (fun (x : prod_eqType A B)(a : A) => a = (fst x)).
exists (fun (x : prod_eqType A B)(b : B) => b = (snd x)).
split.
apply functional_extensionality.
move => a.
apply functional_extensionality.
move => b.
apply prop_extensionality_ok.
split; move => H.
apply I.
exists (a,b).
by [simpl].
split.
apply functional_extensionality.
move => x.
apply functional_extensionality.
move => x0.
apply prop_extensionality_ok.
split.
repeat elim.
move => a.
elim => H H0.
elim => b.
elim => H1 H2.
rewrite (surjective_pairing x0) -H0 -H2 H H1.
apply surjective_pairing.
move => H.
rewrite H.
split.
by [exists (fst x0)].
by [exists (snd x0)].
split.
move => a a0.
elim => x.
elim => H H0.
by [rewrite H H0].
move => b b0.
elim => x.
elim => H H0.
by [rewrite H H0].
Qed.