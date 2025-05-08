From mathcomp Require Export ssreflect.ssreflect ssreflect.eqtype ssrfun bigop ssrbool.
Require Export Logic.ClassicalFacts.

(** %
\section{このライブラリについて}
\begin{screen}
\begin{itemize}
 \item このライブラリは河原康雄先生の ``関係の理論 - Dedekind 圏概説 -'' をもとに制作されている.
 \item 現状サポートしているのは,
 \begin{itemize}
  \item 1.4 節大半, 1.5 - 1.6 節全部
  \item 2.1 - 2.3 節全部, 2.4 - 2.5 節大半, 2.6 節全部, 2.7 節大半, 2.8 節有理性
  \item 4.2 - 4.3 節全部, 4.4 - 4.5 節大半, 4.6 節命題 4.6.1, 4.7 節大半, 4.8 節命題 4.8.1, 4.9 節全部
  \item 5.1 節大半, 5.2 - 5.3 節一部
 \end{itemize}
 といったところである.
 \item 第 3 章以外でカバーしていない箇所は, 基礎的もしくは自明な補題, Coq での定式化が難しい定義や補題, 証明の正当性が示しきれなかった補題, 汎用性の低い一部の記号などである.
\end{itemize}
\end{screen}
% **)

(** %
\section{定義}
\begin{itemize}
\item $A$, $B$ を \verb|eqType| として,
$A$ から $B$ への関係の型を $(\verb|Rel | A \ B)$ と書き,
$A \to B \to \verb|Prop|$ として定義する.
本文中では型 $(\verb|Rel | A \ B)$ を $A \rel B$ と書く.
\item 関係 $\alpha: A \rel B$ の
逆関係 $\alpha^\sharp : B \rel A$ は
$(\verb|inverse | \alpha)$ で,
\verb|Coq| では $(\alpha \verb| #|)$ と記述する.
\item 2 つの関係 $\alpha: A \rel B$,
$\beta: B \rel C$ の
合成関係 $\alpha \cdot \beta \mbox{(or $\alpha \beta$)} :A \rel C$ は
$(\verb|composite | \alpha \ \beta)$ で,
$(\alpha \verb| ・ | \beta)$ と記述する.
\item 剰余合成関係 $\alpha \rhd \beta:A \rel C$ は
$(\verb|residual | \alpha \ \beta)$ で,
$(\alpha \verb| △ | \beta)$ と記述する.
\item 恒等関係 $\id_A: A \rel A$ は
$(\verb|identity | A)$ で,
$(\verb|Id | A)$ と記述する.
\item 空関係 $\phi_{AB} : A \rel B$ は
$(\verb|empty | A \ B)$ で,
$(\verb|φ | A \ B)$ と記述する.
\item 全関係 $\nabla_{AB} : A \rel B$ は
$(\verb|universal | A \ B)$ で,
$(\verb|∇ | A \ B)$ と記述する.
\item 2 つの関係 $\alpha: A \rel B$,
$\beta: A \rel B$ の
和関係 $\alpha \sqcup \beta: A \rel B$ は
$(\verb|cup | \alpha \ \beta)$ で,
$(\alpha \verb| ∪ | \beta)$ と記述する.
\item 共通関係 $\alpha \sqcap \beta: A \rel B$ は
$(\verb|cap | \alpha \ \beta)$ で,
$(\alpha \verb| ∩ | \beta)$ と記述する.
\item 相対擬補関係 $\alpha \Rightarrow \beta : A \rel B$ は
$(\verb|rpc | \alpha \ \beta)$ で,
$(\alpha \verb| >> | \beta)$ と記述する.
\item 関係 $\alpha: A \rel B$ の
補関係 $\alpha^- : A \rel B$ は
$(\verb|complement | \alpha)$ で,
\verb|Coq| では $(\alpha \verb| ^|)$ と記述する.
\item 2 つの関係 $\alpha: A \rel B$,
$\beta: A \rel B$ の
差関係 $\alpha - \beta : A \rel B$ は
$(\verb|difference | \alpha \ \beta)$ で,
$(\alpha \verb| -- | \beta)$ と記述する.
\item \verb|(cupP)| と
\verb|(capP)| は添字付の和関係と共通関係であり, 述語 $P$ に対し,
$\{ f(\alpha) \mid P(\alpha) \}$ の和関係, 共通関係を表す.
\item また, 1 点集合 $I= \{ * \}$ は \verb|i| と表記する.
\item なお, 通常の共通関係, 和関係も添字付のもので表現することができるため,
ここではそれを用いて表記する.
\item 後で述べるように, 剰余合成 $\alpha \rhd \beta$ も
$(\alpha \cdot \beta^-)^-$ のように表現することは可能だが,
``剰余合成が存在すれば, それは $(\alpha \cdot \beta^-)^-$ に等しい''
というレベルのものであるため, 剰余合成に関する公理はやはり必要となる.
\end{itemize}

表\ref{notation}に関係の表記についてまとめる.

\begin{table}
\begin{center}
\begin{tabular}{|l|c|l|c|} \hline
 & 数式 & \hfil Coq \hfil & Notation\\ \hline\hline
逆関係 &
$\alpha^\sharp$ & 
$(\verb|inverse | \alpha)$ &
$(\alpha \verb| #|)$ \\ \hline
合成関係 &
$\alpha \cdot \beta$ & 
$(\verb|composite | \alpha \ \beta)$ &
$(\alpha \verb| ・ | \beta)$ \\ \hline
剰余合成関係 &
$\alpha \rhd \beta$ & 
$(\verb|residual | \alpha \ \beta)$ &
$(\alpha \verb| △ | \beta)$ \\ \hline
恒等関係 &
$\id_A$ & 
$(\verb|identity | A)$ &
$(\verb|Id | A)$ \\ \hline
空関係 &
$\phi_{AB}$ & 
$(\verb|empty | A \ B)$ &
$(\verb|φ | A \ B)$ \\ \hline
全関係 &
$\nabla_{AB}$ & 
$(\verb|universal | A \ B)$ &
$(\verb|∇ | A \ B)$ \\ \hline
和関係 &
$\alpha \sqcup \beta$ & 
$(\verb|cup | \alpha \ \beta)$ &
$(\alpha \verb| ∪ | \beta) $ \\ \hline
共通関係 &
$\alpha \sqcap \beta$ & 
$(\verb|cap | \alpha \ \beta)$ &
$(\alpha \verb| ∩ | \beta)$ \\ \hline
相対擬補関係 &
$\alpha \Rightarrow \beta$ & 
$(\verb|rpc | \alpha \ \beta)$ &
$(\alpha \verb| >> | \beta)$ \\ \hline
補関係 &
$\alpha^-$ & 
$(\verb|complement | \alpha)$ &
$(\alpha \verb| ^|)$ \\ \hline
差関係 &
$\alpha - \beta$ & 
$(\verb|difference | \alpha \ \beta)$ &
$(\alpha \verb| -- | \beta)$ \\ \hline
添字付和関係 &
$\sqcup_{P(\alpha)} f(\alpha)$ & 
$(\verb|cupP | P \ f)$ &
$(\verb|∪_{| P \verb|} | f)$ \\ \hline
添字付共通関係 &
$\sqcap_{P(\alpha)} f(\alpha)$ & 
$(\verb|capP | P \ f)$ &
$(\verb|∩_{| P \verb|} | f)$ \\ \hline
\end{tabular}
\end{center}
\caption{関係の表記について}\label{notation}
\end{table}
% **)

Axiom prop_extensionality_ok : prop_extensionality.

Definition Rel (A B : eqType) := A -> B -> Prop.

Module Type Relation.

Parameter inverse : (forall A B : eqType, Rel A B -> Rel B A).
Notation "a #" := (inverse _ _ a) (at level 20).
Parameter composite : (forall A B C : eqType, Rel A B -> Rel B C -> Rel A C).
Notation "a '・' b" := (composite _ _ _ a b) (at level 50).
Parameter residual : (forall A B C : eqType, Rel A B -> Rel B C -> Rel A C).
Notation "a '△' b" := (residual _ _ _ a b) (at level 50).

Parameter identity : (forall A : eqType, Rel A A).
Notation "'Id'" := identity.
Parameter empty : (forall A B : eqType, Rel A B).
Notation "'φ'" := empty.
Parameter universal : (forall A B : eqType, Rel A B).
Notation "'∇'" := universal.

Parameter include : (forall A B : eqType, Rel A B -> Rel A B -> Prop).
Notation "a '⊆' b" := (include _ _ a b) (at level 50).
(* Rel_Eq (≡) は, こちらでは採用していない. 集合論での定義と違い a ≡ b -> a = b が示せなくなるため, 証明での rewrite や replace が今まで以上に困難になると予想されるためである. *)

Parameter cupP : (forall A B C D : eqType, (Rel C D -> Prop) -> (Rel C D -> Rel A B) -> Rel A B).
Notation "'∪_{' p '}'  f" := (cupP _ _ _ _ p f) (at level 50).
Parameter capP : (forall A B C D : eqType, (Rel C D -> Prop) -> (Rel C D -> Rel A B) -> Rel A B).
Notation "'∩_{' p '}'  f" := (capP _ _ _ _ p f) (at level 50).
(* 本来なら sig_eqType で "Rel C D の元のうち述語 p を満たすもの" を指定したいところだが, その場合 p の型を L -> bool にする必要があるため面倒 *)

Definition cup {A B : eqType} (alpha beta : Rel A B)
 := ∪_{fun gamma : Rel A B => gamma = alpha \/ gamma = beta} id.
Notation "a '∪' b" := (cup a b) (at level 50).
Definition cap {A B : eqType} (alpha beta : Rel A B)
 := ∩_{fun gamma : Rel A B => gamma = alpha \/ gamma = beta} id.
Notation "a '∩' b" := (cap a b) (at level 50).
Parameter rpc : (forall A B : eqType, Rel A B -> Rel A B -> Rel A B).
Notation "a '>>' b" := (rpc _ _ a b) (at level 50).
Definition complement {A B : eqType} (alpha : Rel A B) := alpha >> φ A B.
Notation "a '^'" := (complement a) (at level 20).
Definition difference {A B : eqType} (alpha beta : Rel A B) := alpha ∩ beta ^.
Notation "a -- b" := (difference a b) (at level 50).
(* complement および difference は, Dedekind 圏の公理に登場しないため, Parameter ではなく Definition で定義している. *)

Notation "'i'" := unit.

(** %
\section{関数の定義}
\begin{screen}
$\alpha :A \rel B$ に対し, 全域性 \verb|total_r|, 一価性 \verb|univalent_r|, 関数 \verb|function_r|, 全射 \verb|surjective_r|, 単射 \verb|injective_r|, 全単射 \verb|bijection_r| を以下のように定義する.
\begin{itemize}
\item \verb|total_r| : $id_A \sqsubseteq \alpha \cdot \alpha^\sharp$
\item \verb|univalent_r| : $\alpha^\sharp \cdot \alpha \sqsubseteq id_B$
\item \verb|function_r| : $id_A \sqsubseteq \alpha \cdot \alpha^\sharp \land \alpha^\sharp \cdot \alpha \sqsubseteq id_B$
\item \verb|surjection_r| : $id_A \sqsubseteq \alpha \cdot \alpha^\sharp \land \alpha^\sharp \cdot \alpha = id_B$
\item \verb|injection_r| : $id_A = \alpha \cdot \alpha^\sharp \land \alpha^\sharp \cdot \alpha \sqsubseteq id_B$
\item \verb|bijection_r| : $id_A = \alpha \cdot \alpha^\sharp \land \alpha^\sharp \cdot \alpha = id_B$
\end{itemize}
\end{screen}
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
\begin{axiom}[comp\_id\_l, comp\_id\_r]
Let $\alpha :A \rel B$. Then,
$$
id_A \cdot \alpha = \alpha \cdot id_B = \alpha.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom1a := forall (A B : eqType)(alpha : Rel A B), Id A ・ alpha = alpha.
Axiom comp_id_l : axiom1a.
Definition axiom1b := forall (A B : eqType)(alpha : Rel A B), alpha ・ Id B = alpha.
Axiom comp_id_r : axiom1b.

(** %
\begin{screen}
\begin{axiom}[comp\_assoc]
Let $\alpha :A \rel B$, $\beta :B \rel C$, and $\gamma :C \rel D$. Then,
$$
(\alpha \cdot \beta) \cdot \gamma = \alpha \cdot (\beta \cdot \gamma).
$$
\end{axiom}
\end{screen}
% **)
Definition axiom2 :=
 forall (A B C D : eqType)(alpha : Rel A B)(beta : Rel B C)(gamma : Rel C D),
 (alpha ・ beta) ・ gamma = alpha ・ (beta ・ gamma).
Axiom comp_assoc : axiom2.

(** %
\begin{screen}
\begin{axiom}[inc\_refl]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqsubseteq \alpha.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom3 := forall (A B : eqType)(alpha : Rel A B), alpha ⊆ alpha.
Axiom inc_refl : axiom3.

(** %
\begin{screen}
\begin{axiom}[inc\_trans]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \land \beta \sqsubseteq \gamma \Rightarrow \alpha \sqsubseteq \gamma.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom4 := forall (A B : eqType)(alpha beta gamma : Rel A B),
 alpha ⊆ beta -> beta ⊆ gamma -> alpha ⊆ gamma.
Axiom inc_trans : axiom4.

(** %
\begin{screen}
\begin{axiom}[inc\_antisym]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \land \beta \sqsubseteq \alpha \Rightarrow \alpha = \beta.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom5 := forall (A B : eqType)(alpha beta : Rel A B),
 alpha ⊆ beta -> beta ⊆ alpha -> alpha = beta.
Axiom inc_antisym : axiom5.

(** %
\begin{screen}
\begin{axiom}[inc\_empty\_alpha]
Let $\alpha :A \rel B$. Then,
$$
\phi_{AB} \sqsubseteq \alpha.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom6 := forall (A B : eqType)(alpha : Rel A B), φ A B ⊆ alpha.
Axiom inc_empty_alpha : axiom6.

(** %
\begin{screen}
\begin{axiom}[inc\_alpha\_universal]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqsubseteq \nabla_{AB}.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom7 := forall (A B : eqType)(alpha : Rel A B), alpha ⊆ ∇ A B.
Axiom inc_alpha_universal : axiom7.

(** %
\begin{screen}
\begin{axiom}[inc\_capP, inc\_cap]
\begin{verbatim}
\end{verbatim}
\begin{enumerate}
\par \par
\item {\bf inc\_capP :} Let $\alpha :A \rel B$, $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
\alpha \sqsubseteq (\sqcap_{P(\beta)} f(\beta)) \Leftrightarrow \forall \beta :C \rel D, P(\beta) \Rightarrow \alpha \sqsubseteq f(\beta).
$$
\item {\bf inc\_cap :} Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq (\beta \sqcap \gamma) \Leftrightarrow \alpha \sqsubseteq \beta \land \alpha \sqsubseteq \gamma.
$$
\end{enumerate}
\end{axiom}
\end{screen}
% **)
Definition axiom8a :=
 forall (A B C D : eqType)
 (alpha : Rel A B)(f : Rel C D -> Rel A B)(P : Rel C D -> Prop),
 alpha ⊆ (∩_{P} f) <-> forall beta : Rel C D, P beta -> alpha ⊆ f beta.
Axiom inc_capP : axiom8a.
Definition axiom8b := forall (A B : eqType)(alpha beta gamma : Rel A B),
 alpha ⊆ (beta ∩ gamma) <-> (alpha ⊆ beta) /\ (alpha ⊆ gamma).
Lemma inc_cap : axiom8b.
Proof.
move => A B alpha beta gamma.
rewrite inc_capP.
split; move => H.
split; apply H.
by [left].
by [right].
move => delta H0.
case H0 => H1; rewrite H1; apply H.
Qed.

(** %
\begin{screen}
\begin{axiom}[inc\_cupP, inc\_cup]
\begin{verbatim}
\end{verbatim}
\begin{enumerate}
\item {\bf inc\_cupP :} Let $\alpha :A \rel B$, $f:(C \rel D) \to (A \rel B)$ and $P$ : predicate. Then,
$$
(\sqcup_{P(\beta)} f(\beta)) \sqsubseteq \alpha \Leftrightarrow \forall \beta :C \rel D, P(\beta) \Rightarrow f(\beta) \sqsubseteq \alpha.
$$
\item {\bf inc\_cup :} Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
(\beta \sqcup \gamma) \sqsubseteq \alpha \Leftrightarrow \beta \sqsubseteq \alpha \land \gamma \sqsubseteq \alpha.
$$
\end{enumerate}
\end{axiom}
\end{screen}
% **)
Definition axiom9a :=
 forall (A B C D : eqType)
 (alpha : Rel A B)(f : Rel C D -> Rel A B)(P : Rel C D -> Prop),
 (∪_{P} f) ⊆ alpha <-> forall beta : Rel C D, P beta -> f beta ⊆ alpha.
Axiom inc_cupP : axiom9a.
Definition axiom9b := forall (A B : eqType)(alpha beta gamma : Rel A B),
 (beta ∪ gamma) ⊆ alpha <-> (beta ⊆ alpha) /\ (gamma ⊆ alpha).
Lemma inc_cup : axiom9b.
Proof.
move => A B alpha beta gamma.
rewrite inc_cupP.
split; move => H.
split; apply H.
by [left].
by [right].
move => delta H0.
case H0 => H1; rewrite H1; apply H.
Qed.

(** %
\begin{screen}
\begin{axiom}[inc\_rpc]
Let $\alpha , \beta , \gamma :A \rel B$. Then,
$$
\alpha \sqsubseteq (\beta \Rightarrow \gamma) \Leftrightarrow (\alpha \sqcap \beta) \sqsubseteq \gamma.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom10 := forall (A B : eqType)(alpha beta gamma : Rel A B),
 alpha ⊆ (beta >> gamma) <-> (alpha ∩ beta) ⊆ gamma.
Axiom inc_rpc : axiom10.

(** %
\begin{screen}
\begin{axiom}[inv\_invol]
Let $\alpha :A \rel B$. Then,
$$
(\alpha^\sharp)^\sharp = \alpha.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom11 := forall (A B : eqType)(alpha : Rel A B), (alpha #) # = alpha.
Axiom inv_invol : axiom11.

(** %
\begin{screen}
\begin{axiom}[comp\_inv]
Let $\alpha :A \rel B$ and $\beta :B \rel C$. Then,
$$
(\alpha \cdot \beta)^\sharp = \beta^\sharp \cdot \alpha^\sharp.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom12 := forall (A B C : eqType)(alpha : Rel A B)(beta : Rel B C),
 (alpha ・ beta) # = (beta # ・ alpha #).
Axiom comp_inv : axiom12.

(** %
\begin{screen}
\begin{axiom}[inc\_inv]
Let $\alpha , \beta :A \rel B$. Then,
$$
\alpha \sqsubseteq \beta \Rightarrow \alpha^\sharp \sqsubseteq \beta^\sharp.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom13 :=
 forall (A B : eqType)(alpha beta : Rel A B), alpha ⊆ beta -> alpha # ⊆ beta #.
Axiom inc_inv : axiom13.

(** %
\begin{screen}
\begin{axiom}[dedekind]
Let $\alpha :A \rel B$, $\beta :B \rel C$, and $\gamma :A \rel C$. Then,
$$
(\alpha \cdot \beta) \sqcap \gamma \sqsubseteq (\alpha \sqcap (\gamma \cdot \beta^\sharp)) \cdot (\beta \sqcap (\alpha^\sharp \cdot \gamma)).
$$
\end{axiom}
\end{screen}
% **)
Definition axiom14 :=
 forall (A B C : eqType)(alpha : Rel A B)(beta : Rel B C)(gamma : Rel A C),
 ((alpha ・ beta) ∩ gamma)
 ⊆ ((alpha ∩ (gamma ・ beta #)) ・ (beta ∩ (alpha # ・ gamma))).
Axiom dedekind : axiom14.

(** %
\begin{screen}
\begin{axiom}[inc\_residual]
Let $\alpha :A \rel B$, $\beta :B \rel C$, and $\gamma :A \rel C$. Then,
$$
\gamma \sqsubseteq (\alpha \rhd \beta) \Leftrightarrow \alpha^\sharp \cdot \gamma \sqsubseteq \beta.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom15 :=
 forall (A B C : eqType)(alpha : Rel A B)(beta : Rel B C)(gamma : Rel A C),
 gamma ⊆ (alpha △ beta) <-> (alpha # ・ gamma) ⊆ beta.
Axiom inc_residual : axiom15.

(** %
\subsection{排中律}
\begin{screen}
Dedekind 圏の公理のほかに, 以下の ``排中律'' を仮定すれば, 与えられる圏は Schr$\ddot{\mbox{o}}$der 圏となり, Bool 代数の性質も満たされる. ちなみに剰余合成は補関係から定義可能なので, 本来 Schr$\ddot{\mbox{o}}$der 圏には剰余合成に関する公理は存在しない.
\begin{axiom}[complement\_classic]
Let $\alpha :A \rel B$. Then,
$$
\alpha \sqcup \alpha^- = \nabla_{AB}
$$
\end{axiom}
\end{screen}
% **)
Definition axiom16 := forall (A B : eqType)(alpha : Rel A B),
 alpha ∪ alpha ^ = ∇ A B.
Axiom complement_classic : axiom16.

(** %
\subsection{単域}
\begin{screen}
1 点集合 $I$ が単域となるための条件は
$$
\phi_{II} \neq id_I \land id_I = \nabla_{II} \land \forall X, \nabla_{XI} \cdot \nabla_{IX} = \nabla_{XX}
$$
だが, Rel の定義から左 2 つは証明できるため, 右の式だけ仮定する.
\begin{axiom}[unit\_universal]
$$
\nabla_{AI} \cdot \nabla_{IA} = \nabla_{AA}
$$
\end{axiom}
\end{screen}
% **)
Definition axiom17 := forall (A : eqType), ∇ A i ・ ∇ i A = ∇ A A.
Axiom unit_universal : axiom17.

(** %
\subsection{選択公理}
\begin{screen}
この ``選択公理'' を仮定すれば, 排中律と単域の存在(厳密には全域性公理)を利用して点公理を導出できる.
\begin{axiom}[axiom\_of\_choice]
Let $\alpha :A \rel B$ be a total relation. Then,
$$
\exists \beta :A \to B, \beta \sqsubseteq \alpha.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom18 := forall (A B : eqType)(alpha : Rel A B),
 total_r alpha -> exists beta : Rel A B, function_r beta /\ beta ⊆ alpha.
Axiom axiom_of_choice : axiom18.

(** %
\subsection{関係の有理性}
\begin{screen}
集合論では色々インポートしながら頑張って証明したので, できればそちらもご覧ください.
\begin{axiom}[rationality]
Let $\alpha :A \rel B$. Then,
$$
\exists R, \exists f:R \to A, \exists g:R \to B, \alpha = f^\sharp \cdot g \land f \cdot f^\sharp \sqcap g \cdot g^\sharp = id_R.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom19 := forall (A B : eqType)(alpha : Rel A B),
 exists (R : eqType)(f : Rel R A)(g : Rel R B),
 function_r f /\ function_r g /\ alpha = f # ・ g /\ ((f ・ f #) ∩ (g ・ g #)) = Id R.
Axiom rationality : axiom19.

(** %
\subsection{直和と直積}
\begin{screen}
任意の直和に対して, 入射対が存在することを仮定する.
\begin{axiom}[pair\_of\_inclusions]
$\exists j:A \to A+B, \exists k:B \to A+B, $
$$
j \cdot j^\sharp = id_A \land k \cdot k^\sharp = id_B \land j \cdot k^\sharp = \phi_{AB} \land j^\sharp \cdot j \sqcup k^\sharp \cdot k = id_{A+B}.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom20 :=
 forall (A B : eqType), exists (j : Rel A (sum A B))(k : Rel B (sum A B)),
 j ・ j # = Id A /\ k ・ k # = Id B /\ j ・ k # = φ A B /\
 (j # ・ j) ∪ (k # ・ k) = Id (sum A B).
Axiom pair_of_inclusions : axiom20.

(** %
\begin{screen}
任意の直積に対して, 射影対が存在することを仮定する. \\
実は有理性公理(Axiom 19)があれば直積の公理は必要ないのだが, Axiom 19 の準用では直積が ``存在する'' ことまでしか示してくれないので, ``直積として \verb|prod_eqType A B| を用いてよい'' ことを公理の中に含めたものを用意しておく.
\begin{axiom}[pair\_of\_projections]
$\exists p:A \times B \to A, \exists q:A \times B \to B,$
$$
p^\sharp \cdot q = \nabla_{AB} \land p \cdot p^\sharp \sqcap q \cdot q^\sharp = id_{A \times B}.
$$
\end{axiom}
\end{screen}
% **)
Definition axiom21 :=
 forall (A B : eqType), exists (p : Rel (prod A B) A)(q : Rel (prod A B) B),
 p # ・ q = ∇ A B /\ (p ・ p #) ∩ (q ・ q #) = Id (prod A B) /\ univalent_r p /\ univalent_r q.
Axiom pair_of_projections : axiom21.

End Relation.
