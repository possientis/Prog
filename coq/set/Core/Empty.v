Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.ToList.

Lemma empty_charac : forall (z:set), ~ (z :: Nil).
Proof.
    intros z H. apply toListElem in H. 
    destruct H as [z' [H1 [H2 H3]]]. inversion H1.
Qed.

(* The existence of the empty set is true in 'set'                              *)
Theorem empty_set : exists (x:set), forall (z:set), ~ (z :: x).  
Proof.
    exists Nil. apply empty_charac.
Qed.
