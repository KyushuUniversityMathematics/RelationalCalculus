Require Import Basic_Notations_Set.
Require Import Basic_Lemmas.
Require Import Relation_Properties.

Module main (def : Relation).
Import def.
Module Basic_Lemmas := Basic_Lemmas.main def.
Module Relation_Properties := Relation_Properties.main def.
Import Basic_Lemmas Relation_Properties.

(** %
\section{Tactic 用の補題}
\begin{screen}
$\alpha = \beta$ の形では自動計算がしづらいので, 事前に $\alpha \sqsubseteq \beta \land \beta \sqsubseteq \alpha$ の形に変換しておく.
\end{screen}
% **)
Lemma inc_antisym_eq {A B : eqType} {alpha beta : Rel A B}:
 alpha = beta <-> alpha ⊆ beta /\ beta ⊆ alpha.
Proof.
split; move => H.
rewrite H.
split; apply inc_refl.
apply inc_antisym; apply H.
Qed.

(** %
\section{Tactic}
\begin{screen}
ここでは以下の 5 tactics を実装している.
\begin{itemize}
\item \verb|Rel_simpl_rewrite| ... 関数などの定義の書き換え
\item \verb|Rel_simpl_intro| ... 命題間の関係の整理, \verb|inc_antisym_eq| の書き換え
\item \verb|Rel_simpl_comp_inc| ... \verb|comp_inc_compat| 関連の補題の適用
\item \verb|Rel_simpl| ... 証明のための各種動作, 上記 3 tactics を全て含む
\item \verb|Rel_trans| ... \verb|Rel_simpl| に \verb|inc_trans| を組み込んだもの, 引数が必要
\end{itemize}
\end{screen}
% **)
Ltac Rel_simpl_rewrite :=
 rewrite /bijection_r/surjection_r/injection_r;
 rewrite /function_r/total_r/univalent_r.
Ltac Rel_simpl_intro :=
 Rel_simpl_rewrite;
 repeat match goal with
          | [_ : _ |- (_ /\ _) -> _ ] => elim
          | [_ : _ |- _ -> _ ] => intro
          | [_ : _ |- _ /\ _ ] => split
          | [_ : _ |- _ <-> _ ] => split
          | [_ : _ |- _ = _ ] => rewrite inc_antisym_eq
          | [ H : _ = _ |- _ ] => rewrite inc_antisym_eq in H
        end.
Ltac Rel_simpl_comp_inc :=
 repeat match goal with
          | [ H : ?g ⊆ Id _ |- (?f ・ ?g) ⊆ ?f ] => apply (comp_inc_compat_ab_a H)
          | [ H : ?g ⊆ Id _ |- (?g ・ ?f) ⊆ ?f ] => apply (comp_inc_compat_ab_b H)
          | [ H : Id _ ⊆ ?g |- ?f ⊆ (?f ・ ?g) ] => apply (comp_inc_compat_a_ab H)
          | [ H : Id _ ⊆ ?g |- ?f ⊆ (?g ・ ?f) ] => apply (comp_inc_compat_b_ab H)
          | [_ : _ |- _ ] => repeat rewrite -comp_assoc; (apply comp_inc_compat_ab_a'b || apply comp_inc_compat_b_ab || apply comp_inc_compat_ab_b)
          | [_ : _ |- _ ] => repeat rewrite comp_assoc; (apply comp_inc_compat_ab_ab' || apply comp_inc_compat_a_ab || apply comp_inc_compat_ab_a)
          | [_ : _ |- (_ ・ _) ⊆ (_ ・ _) ] => apply comp_inc_compat
        end.
Ltac Rel_simpl :=
 Rel_simpl_intro;
 repeat match goal with
          | [ f : Rel _ _, H : _ ⊆ _ |- _ ] => rewrite (@inv_invol _ _ f) in H
        end;
 repeat match goal with
          | [_ : _ |- ?f ⊆ ?f ] => apply inc_refl
          | [ H : ?P |- ?P ] => apply H
          | [ H : ?f ⊆ ?g, H0 : ?g ⊆ ?h |- ?f ⊆ ?h ] => apply (@inc_trans _ _ _ _ _ H H0)
          | [_ : _ |- (_ #) ⊆ (_ #) ] => apply inc_inv
          | [ A : eqType, B : eqType, C : eqType |- _ ] => rewrite (@comp_inv A B C)
          | [ f : Rel _ _ |- _ ] => rewrite (@inv_invol _ _ f)
          | [ H : (Id _) ⊆ _ |- (Id _) ⊆ _ ] => apply (@inc_trans _ _ _ _ _ H)
          | [ H : _ ⊆ (Id _)  |- _ ⊆ (Id _) ] => apply (fun H' => (@inc_trans _ _ _ _ _ H' H))
          | [_ : _ |- _ ] => Rel_simpl_comp_inc
        end.
Ltac Rel_trans f :=
 apply (@inc_trans _ _ _ f); Rel_simpl.

(** %
\section{実験}
\begin{screen}
\verb|Functions_Mappings.v| の補題には, 単一の tactic のみで解けるものも多い.
\end{screen}
% **)

Lemma total_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 total_r alpha -> total_r beta -> total_r (alpha ・ beta).
Proof.
Rel_simpl.
Qed.

Lemma univalent_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r alpha -> univalent_r beta -> univalent_r (alpha ・ beta).
Proof.
Rel_simpl.
Qed.

Lemma function_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 function_r alpha -> function_r beta -> function_r (alpha ・ beta).
Proof.
Rel_simpl.
Qed.

Lemma univalent_comp2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 univalent_r (alpha ・ beta) -> total_r (alpha #) -> univalent_r beta.
Proof.
Rel_simpl.
Qed.

Lemma total_inc {A B : eqType} {alpha beta : Rel A B}:
 total_r alpha -> alpha ⊆ beta -> total_r beta.
Proof.
Rel_simpl.
Qed.

Lemma univalent_inc {A B : eqType} {alpha beta : Rel A B}:
 univalent_r alpha -> beta ⊆ alpha -> univalent_r beta.
Proof.
Rel_simpl.
Qed.

Lemma function_inc {A B : eqType} {alpha beta : Rel A B}:
 function_r alpha -> function_r beta -> alpha ⊆ beta -> alpha = beta.
Proof.
Rel_simpl.
Rel_trans ((alpha ・ alpha #) ・ beta).
Qed.

Lemma function_move1 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 function_r alpha -> (gamma ⊆ (alpha ・ beta) <-> (alpha # ・ gamma) ⊆ beta).
Proof.
Rel_simpl.
Rel_trans ((alpha # ・ alpha) ・ beta).
Rel_trans ((alpha ・ alpha #) ・ gamma).
Qed.

Lemma function_move2 {A B C : eqType} {alpha : Rel A B} {beta : Rel B C} {gamma : Rel A C}:
 function_r beta -> ((alpha ・ beta) ⊆ gamma <-> alpha ⊆ (gamma ・ beta #)).
Proof.
Rel_simpl.
Rel_trans ((alpha ・ beta) ・ beta #).
Rel_trans ((gamma ・ beta #) ・ beta).
Qed.

Lemma surjection_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 surjection_r alpha -> surjection_r beta -> surjection_r (alpha ・ beta).
Proof.
Rel_simpl.
Qed.

Lemma injection_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 injection_r alpha -> injection_r beta -> injection_r (alpha ・ beta).
Proof.
Rel_simpl.
Qed.

Lemma bijection_comp {A B C : eqType} {alpha : Rel A B} {beta : Rel B C}:
 bijection_r alpha -> bijection_r beta -> bijection_r (alpha ・ beta).
Proof.
Rel_simpl.
Qed.

Lemma bijection_inv_corollary {A B : eqType} {alpha : Rel A B}:
 bijection_r alpha -> bijection_r (alpha #).
Proof.
Rel_simpl.
Qed.

End main.