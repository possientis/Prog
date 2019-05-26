Require Import Relation.
Require Import Fol.P.

Definition congruent (v:Type) (r:Rel (P v)) : Prop := 
    (forall (p1 p2 q1 q2:P v), r p1 q1 -> r p2 q2 -> r (Imp p1 p2) (Imp q1 q2)) /\
    (forall (x:v) (p1 q1:P v), r p1 q1 -> r (All x p1) (All x q1)).

Arguments congruent {v} _.

Definition congruence (v:Type) (r:Rel (P v)) : Prop :=
   equivalence r /\ congruent r. 

Arguments congruence {v} _.


Lemma fmap_congruence : forall (v w:Type) (f:v -> w) (r:Rel (P w)),
    congruence r -> congruence (fun (p q:P v) => r (fmap f p) (fmap f q)).
Proof.
    intros v w f r [H1 [HImp HAll]]. 
    unfold equivalence in H1. destruct H1 as [Refl [Symm Tran]].
    unfold reflexive in Refl.
    unfold symmetric in Symm.
    unfold transitive in Tran.
    split.
    - split.
        + unfold reflexive. intros x. apply Refl.
        + split.
            { unfold symmetric. intros x y. apply Symm. }
            { unfold transitive.  intros x y z. apply Tran. }
    - split.
        + intros s1 s2 t1 t2. apply HImp.
        + intros x s1 t1. apply HAll.
Qed. 
  
