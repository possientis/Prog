Require Import Logic.Axiom.Dec.

Inductive G (p : nat -> Prop) : nat -> Prop :=
| mkG : forall (n:nat), (~ p n -> G p (S n)) -> G p n
.

Lemma pn_imp_Gn : forall (p:nat -> Prop) (n:nat), p n -> G p n.
Proof.
    intros p n H1. constructor. intros H2. apply H2 in H1. contradiction.
Defined.

Lemma GSn_imp_Gn : forall (p:nat -> Prop) (n:nat), G p (S n) -> G p n.
Proof.
    intros p n H1. constructor. intros H2. assumption.
Defined.

Lemma Gn_imp_G0 : forall (p:nat -> Prop) (n:nat), G p n -> G p 0.
Proof.
    intros p. induction n as [|n IH].
    - auto.
    - intros H1.  apply IH, GSn_imp_Gn. assumption.
Defined.

Definition elimG 
    (p:nat -> Prop) 
    (c:nat -> Type)
    (g: forall (n:nat), (~ p n -> c (S n)) -> c n)
    : forall (n:nat), G p n -> c n 
    := fix k (n:nat) (H:G p n) : c n := g n 
        (fun e => k (S n) 
            ( match H with
              | mkG _ _ H => H
              end e)).

Definition Gn_to_sig : forall (p:nat -> Prop) (q:pDec p) (n:nat),
    G p n -> sig p.
Proof.
    intros p q. apply elimG. intros n H1. destruct (q n) as [H2|H2].
    - exact (exist _ n H2). 
    - apply H1. assumption.
Defined.

(* When dealing with a computationally decidable predicate p, it is possible to *)
(* extract a witness of the predicate being satisfied, simply from a proof of   *)
(* existence. Somehow we are able to bypass the 'Prop' restriction.             *)
Theorem witness : forall (p:nat -> Prop) (q:pDec p),
    (exists (n:nat), p n) -> sig p.
Proof.
    intros p q H1. apply Gn_to_sig with 0; try assumption. destruct H1 as [n H1].
    apply Gn_imp_G0 with n. apply pn_imp_Gn. assumption.
Defined.
