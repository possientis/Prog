Require Import Logic.Lam.Syntax.
Require Import Logic.Lam.Functor.

Require Import Logic.Rel.Properties.

Definition congruent (v:Type) (r:Rel (T v)) : Prop := 
    (forall (s1 s2 t1 t2:T v), r s1 t1 -> r s2 t2 -> r (App s1 s2) (App t1 t2)) /\
    (forall (x:v) (s1 t1:T v), r s1 t1 -> r (Lam x s1) (Lam x t1)).

Arguments congruent {v} _.

Definition congruence (v:Type) (r:Rel (T v)) : Prop :=
   equivalence r /\ congruent r. 

Arguments congruence {v} _.


Lemma fmap_congruence : forall (v w:Type) (f:v -> w) (r:Rel (T w)),
    congruence r -> congruence (fun (s t:T v) => r (fmap f s) (fmap f t)).
Proof.
    intros v w f r [H1 [HApp HLam]]. 
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
        + intros s1 s2 t1 t2. apply HApp.
        + intros x s1 t1. apply HLam.
Qed. 
    

