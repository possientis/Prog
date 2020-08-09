Definition Decider (a:Type) (p:a -> Prop) (f:a -> bool) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments Decider {a}.

Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.

Definition Sig_proj1 (a:Type) (p:a -> Type) (y:Sig p) : a :=
    match y with
    | Ex x _ => x
    end.

Arguments Sig_proj1 {a} {p}.
 
Definition Sig_proj2 (a:Type) (p:a -> Type) (y:Sig p) : p (Sig_proj1 y) :=
    match y with
    | Ex x H => H
    end.

(*
Definition T1 : forall (a:Type) (p:a -> Prop),
    Sig (Decider p) -> forall (x:a), {p x} + {~ p x}.
Proof.
    intros a p H1. remember (Decider p) as q eqn:Q.
    revert Q. revert p. destruct H1.
Show.
*)


