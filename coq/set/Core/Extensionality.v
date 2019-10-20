Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.ToList.
Require Import Core.Trans.
Require Import Core.ElemIncl.
Require Import Core.Equal.

Theorem extensionality : forall (x y:set),
    x == y <-> forall (z:set), z :: x <-> z :: y.
Proof.
    intros x y. split.
    - intros [H1 H2]. assumption. 
    - intros H. split.
        + assumption.
        + intros z. split; intros H'; apply toListElem in H'.
            { destruct H' as [x' [H1 [H2 H3]]]. 
              apply toListElem. exists x'. split.
                { assumption. }
                { split.
                    { apply incl_trans with x.
                        { apply elemIncl. apply H. }
                        { assumption. }}
                    { apply incl_trans with x.
                        { assumption. }
                        { apply elemIncl. apply H. }}}}
            { destruct H' as [y' [H1 [H2 H3]]]. 
              apply toListElem. exists y'. split.
                { assumption. }
                { split.
                    { apply incl_trans with y.
                        { apply elemIncl. apply H. }
                        { assumption. }}
                    { apply incl_trans with y.
                        { assumption. }
                        { apply elemIncl. apply H. }}}}
Qed.

Theorem doubleIncl : forall (x y:set), 
    x == y <-> (x <== y) /\ (y <== x).
Proof.
    intros x y. split.
    - intros H. destruct H as [H1 H2]. split; apply elemIncl; apply H1.
    - intros [H1 H2]. apply extensionality. intros z. split; intros H.
        + rewrite elemIncl in H1. apply H1. assumption.
        + rewrite elemIncl in H2. apply H2. assumption.
Qed.

