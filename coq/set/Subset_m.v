Require Import List.

Require Import set.
Require Import nat.
Require Import Order.
Require Import ToList.

Fixpoint subset_m (n:nat) (xs ys:set) : Prop := 
    match n with
    | 0     => True
    | S n   => 
        forall (x:set), elem_m n x xs -> elem_m n x ys 
    end
with elem_m (n:nat) (x xs:set) : Prop :=
    match n with
    | 0     => False
    | S n   =>
        exists (y:set), In y (toList xs) /\ equiv_m n x y
    end
with equiv_m (n:nat) (x y:set) : Prop :=
    match n with
    | 0     => True  
    | S n   => 
        subset_m n x y /\ subset_m n y x
    end
.

Lemma fuel : forall (n:nat) (x y:set),
    order x + order y <= n 
    -> (subset_m n x y <-> subset_m (S n) x y) 
    /\ (elem_m   n x y <-> elem_m   (S n) x y)
    /\ (equiv_m  n x y <-> equiv_m  (S n) x y)
.
Proof.
    induction n as [|n IH].
    - intros x y H. apply le_0 in H. apply sum_0 in H. destruct H as [H1 H2].
      apply order_0 in H1. apply order_0 in H2. rewrite H1, H2. split.
        + simpl. tauto.
        + split.
            { simpl. split. 
                { intros. exists Nil. exfalso. assumption. }
                { intros [z [H H']]. assumption. }
            }
            { simpl. tauto. }
    - intros x y H. remember (S n) as m eqn:E. split.
        + split.
            { intros H1. simpl.

Show.
