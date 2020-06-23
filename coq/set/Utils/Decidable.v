Require Import Utils.LEM.

(* In this module, we define the notion of decidable predicate: let 'a' be a    *)
(* type and 'p:a -> Prop' be a predicate. Saying that the predicate 'p' is      *)
(* decidable is saying 'Dec p' which we are defining as the 'statement':        *)
(*      Dec p := forall (x:a), {p x} + {~p x}                                   *)
(* However, this 'statement' is not a value of type 'Prop'. In other words, it  *)
(* is not a Coq proposition. It is simply a type, namely the type of dependent  *)
(* function q, which given an (x:a) returns a value q x of type {p x} + {~p x}, *)
(* which is either a proof that p x holds, or a proof that ~p x holds.          *)
(* So saying that 'q' is of type 'Dec p', i.e. the jugement 'q:Dec p' is simply *)
(* saying that 'q' is such a dependent function. Informally, we could think of  *)
(* q as 'a proof of Dec p', or a witness to the fact that p is a decidable.     *)

Definition Dec (a:Type) (p:a -> Prop) := forall (x:a), {p x} + {~p x}.

Arguments Dec {a}.

(* Two-fold decidable predicates                                                *)
Definition Dec2 (a b:Type) (p:a -> b -> Prop) := 
    forall (x:a) (y:b), {p x y} + {~p x y}.

Arguments Dec2 {a} {b}.

Lemma Dec2Dec : forall (a b:Type) (p:a -> b -> Prop) (x:a), 
    Dec2 p -> Dec (p x).
Proof.
    intros a b p x H y. apply H.
Qed.

Arguments Dec2Dec {a} {b} {p}.

(* The notion of decidability is too strong. Let us define a weaker notion.     *)
Definition Dec'(a:Type) (p:a -> Prop) := forall (x:a), p x \/ ~p x.

Arguments Dec' {a}.

(* Decidability implies weak decidability.                                      *)
Lemma DecImpliesDec' : forall (a:Type) (p:a -> Prop), Dec p -> Dec' p.
Proof.
    intros a p q x. destruct (q x) as [H|H].
    - left. assumption.
    - right. assumption.
Qed.

Definition Dec2' (a b:Type) (p:a -> b -> Prop) := 
    forall (x:a) (y:b), p x y \/ ~p x y.

Arguments Dec2' {a} {b}.

Lemma Dec2Dec' : forall (a b:Type) (p:a -> b -> Prop) (x:a), 
    Dec2' p -> Dec' (p x).
Proof.
    intros a b p x H y. apply H.
Qed.

(* Weak decidability is weak enough to be implied by LEM.                       *)
Lemma LEMDec' : LEM -> forall (a:Type) (p:a -> Prop), Dec' p.
Proof.
    intros L a p x. apply L.
Qed.

Arguments LEMDec' _ {a}.

Lemma LEMDec2': LEM -> forall (a b:Type) (p:a -> b -> Prop), Dec2' p.
Proof.
    intros L a b p x y. apply L.
Qed.

