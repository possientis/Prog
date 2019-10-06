Require Import List.

Require Import set.
Require Import ToList.

Inductive Exists (P:set -> Prop) : set -> Prop :=
| ExistsH : forall (x:set) (ys:set), P x         -> Exists P (Cons x ys)
| ExistsT : forall (x:set) (ys:set), Exists P ys -> Exists P (Cons x ys)
.

Lemma Exists_toList : forall (P:set -> Prop) (y:set), 
    Exists P y <-> exists (x:set), In x (toList y) /\ P x.
Proof.
    intros P y. split.
    - intros H. induction H as [y ys H|y ys H IH].
        + exists y. split. 
            { left. reflexivity. }
            { assumption. }
        + destruct IH as [x [H1 H2]].
          exists x. split.
            { right. assumption. }
            { assumption. }
    - intros [x [H1 H2]]. revert x H1 H2.
      induction y as [|y _ ys IH].
        + intros x H. inversion H.
        + intros x H H'. destruct H as [H|H].
            { apply ExistsH. rewrite H. assumption. }
            { apply ExistsT. apply IH with x; assumption. }
Qed.


 


