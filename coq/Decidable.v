Axiom LEM : forall (p:Prop), p \/ ~p.

Inductive Dec (p:Prop) : Type :=
| isFalse : ~p -> Dec p
| isTrue  :  p -> Dec p
.

Definition decide (p:Prop) : Dec p.
Proof.
    destruct (LEM p) as [H|H].

Show.
