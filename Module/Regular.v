From mathcomp Require Import fintype finset seq.

Definition language {symbol : finType} := seq symbol -> Prop.

Inductive regular {symbol : finType} : @language symbol -> Prop :=
| reg_empty : regular (fun _ => False)
| reg_epsilon : regular (fun w => w = nil)
| reg_char : forall a, regular (fun w => w = [::a])
| reg_union : forall l1 l2, regular l1 -> regular l2 -> regular (fun w => l1 w \/ l2 w)
| reg_concat : forall l1 l2, regular l1 -> regular l2 -> regular (fun w =>
    exists u v, l1 u /\ l2 v /\ w = u ++ v)
    .

Fixpoint f {symbol:finType}(l:@language symbol)(n:nat):language:=
match n with
|0 => (fun w => w = nil)
|S n' => reg_concat l(f l n')
end.
| reg_star : .
