Ltac find_if :=
    match goal with
    | [ |- if ?X then _ else _ ] => destruct X
    end.

Lemma L1 : forall (a b c:bool),
    if a 
        then if b
            then True
            else True
        else if c
            then True
            else True.
Proof.
    intros. find_if; find_if; constructor.
Qed. 


Ltac find_if_inside :=
    match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    end.

(* find_if cannot crack this *)
Lemma L2 : forall (a b:bool),
    (if a then 42 else 42) = (if b then 42 else 42).
Proof.
    intros. find_if_inside; find_if_inside; reflexivity.
Qed.

Ltac my_tauto :=
    match goal with
    | [ H : ?P |- ?P ]                  => exact H
    | [ |- True ]                       => constructor
    | [ |- _ /\ _ ]                     => constructor
    | [ |- _ -> _ ]                     => intro
    | [ H : False |- _ ]                => destruct H
    | [ H : _ /\ _ |- _ ]               => destruct H
    | [ H : _ \/ _ |- _ ]               => destruct H
    | [ H1 : ?P -> ?Q, H2 : ?P |- _ ]   => specialize (H1 H2)
    | [|- _ \/ _ ]                      => left
    | [|- _ \/ _ ]                      => right
    | [|- _ <-> _ ]                     => split
    end.

Lemma L3 : forall (P Q:Prop), P /\ Q -> Q /\ P.
Proof.
    repeat my_tauto.
Qed.

Ltac my_intro :=
    match goal with
    | [ |- _ -> _ ] => intro
    end.

Lemma L4 : forall (P:Prop), P -> P.
Proof.
    my_intro. my_intro. assumption.
Qed.

Lemma L5 : forall (P Q:Prop), P -> (P -> Q) -> Q.
Proof.
    intros P Q H1 H2. specialize (H2 H1). assumption.
Qed.


(*
Lemma L6 : forall (P Q R:Prop), P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
Proof.
    my_intro.
    my_intro.
    my_intro.



   
Show.
*)

(*
Lemma L7 : forall (P Q:Prop), (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
Proof.
    my_tauto.
Qed.

Lemma L8 : True.
    match goal with
    | [|-_] => intro            (* pattern trivially matches, but tactic fails  *)
    | [|-True] => constructor   (* backtracking then move on to next pattern    *)
    end.                        (* overall success.                             *)
Qed.
*)
