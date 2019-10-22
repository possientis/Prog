Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.Extensionality.

Definition pair (x y:set) : set := Cons x (Cons y Nil).

Notation "{ x , y }" := (pair x y) : set_scope.

Lemma pair_charac : forall (x y z:set), z :: {x,y} <-> (z == x) \/ (z == y).
Proof.
    intros x y z. split.
    - intros H. apply toListElem in H. 
      destruct H as [z' [H1 [H2 H3]]]. destruct H1 as [H1|[H1|H1]].
        + left. apply equal_trans with z'.
            { apply doubleIncl. split; assumption. }
            { rewrite H1. apply equal_refl. }
        + right. apply equal_trans with z'.
            { apply doubleIncl. split; assumption. }
            { rewrite H1. apply equal_refl. }
        + inversion H1.
    - intros [H|H]; apply toListElem.
        + exists x. split.
            { left.  reflexivity. }
            { apply doubleIncl in H. destruct H as [H1 H2]. split; assumption. }
        + exists y. split.
            { right.  left. reflexivity. }
            { apply doubleIncl in H. destruct H as [H1 H2]. split; assumption. }
Qed.

(* The pairing axiom is satisfied in 'set'                                      *)
Theorem pairing : forall (x y:set), exists (z:set), forall (u:set),
    u :: z <-> (u == x) \/ (u == y).
Proof.
    intros x y. exists {x,y}. apply pair_charac. 
Qed.

