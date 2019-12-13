(* NEXT: ===> Pairing                                                           *)


Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.ElemIncl.
Require Import Core.Extensionality.

(* This module contains a few simple results about the empty set. An empty set  *)
(* is of course a set which has no element. There exists an empty set in our    *)
(* model, namely 'Nil'. The following lemma checks that Nil is indeed empty.    *)
(* It is not quite a set theoretic statement since the primitive 'Nil' is a     *)
(* primitive of the Coq meta-theory and not a primitive of a core language.     *)
Lemma emptyCharac : forall (z:set), ~ (z :: Nil).
Proof.
    intros z H. apply toListElem in H. 
    destruct H as [z' [H1 [H2 H3]]]. inversion H1.
Qed.

(* This lemma is useful on a few occasions, allowing us to convert the coq      *)
(* equalty 'x = Nil' to the set theoretic equality 'x == Nil' and vice-versa.   *)
(* This is also a meta-theoretic statement. In effect, this lemma states that   *)
(* the equivalence class of Nil modulo '==' is reduced to a single element.     *)
Lemma emptyIsNil : forall (x:set), x == Nil <-> x = Nil.
Proof.
    intros x. split; intros H.    
    - destruct x as [|x xs].
        + reflexivity.
        + exfalso. apply emptyCharac with x. apply elemIncl with (Cons x xs).
            { apply doubleIncl in H. destruct H as [H1 H2]. assumption. }
            { apply consElem. left. apply equal_refl. }
    - rewrite H. apply equal_refl.
Qed.

(* The existence of the empty set is true in our model                          *)
Theorem emptySet : exists (x:set), forall (z:set), ~ (z :: x).  
Proof.
    exists Nil. apply emptyCharac.
Qed.

(* The empty set is unique: any other set with no element is equal to Nil.      *)
Lemma emptyUnique : forall (x:set), (forall (y:set), ~(y :: x)) -> x == Nil.
Proof.
    intros x H. apply extensionality. intros z. split; intros H'; exfalso.
    - apply (H z). assumption.
    - apply (emptyCharac z). assumption.
Qed.

