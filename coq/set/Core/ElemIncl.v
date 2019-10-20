Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.ToList.
Require Import Core.Trans.


Theorem elemIncl : forall (x y:set), 
    x <== y <-> forall (z:set), z :: x -> z :: y.
Proof.
    intros xs ys. split.
    - intros H z Hz. 
      rewrite toListIncl in H. 
      rewrite toListElem in Hz. destruct Hz as [z' [H1 [H2 H3]]].
      apply toListElem. apply H in H1. apply toListElem in H1.
      destruct H1 as [y [H1 [H4 H5]]]. exists y. split.
      + assumption.
      + split.
        { apply incl_trans with z'; assumption. }
        { apply incl_trans with z'; assumption. }
    - intros H. apply toListIncl. intros z H'. 
      apply H.  apply toListElem. exists z. split.
      + assumption.
      + split; apply incl_refl.
Qed.

