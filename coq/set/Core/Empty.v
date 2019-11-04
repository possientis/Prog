Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.ElemIncl.
Require Import Core.Extensionality.

Lemma emptyCharac : forall (z:set), ~ (z :: Nil).
Proof.
    intros z H. apply toListElem in H. 
    destruct H as [z' [H1 [H2 H3]]]. inversion H1.
Qed.

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

(* The existence of the empty set is true in 'set'                              *)
Theorem emptySet : exists (x:set), forall (z:set), ~ (z :: x).  
Proof.
    exists Nil. apply emptyCharac.
Qed.



