Require Import Le.
Require Import Nat.
Require Import Min.
Require Import Max.
Require Import Plus.
Require Import Mult.

Require Import Utils.nat.

Inductive Color : Set := Red | Black.

Inductive RBTree : Color -> nat -> Set :=
| Leaf      : RBTree Black 0
| RedNode   : forall (n:nat), 
    RBTree Black n -> nat -> RBTree Black n -> RBTree Red n
| BlackNode : forall (c1 c2:Color) (n:nat),
    RBTree c1 n -> nat -> RBTree c2 n -> RBTree Black (S n)
.

Fixpoint depth (c:Color) (n:nat) (f:nat -> nat -> nat) (t:RBTree c n) : nat :=
    match t with
    | Leaf                      => 0
    | RedNode _ t1 _ t2         => S (f (depth _ _ f t1) (depth _ _ f t2))
    | BlackNode _ _ _ t1 _ t2   => S (f (depth _ _ f t1) (depth _ _ f t2))
    end.

Arguments depth {c} {n}.

Theorem depth_min : forall (c:Color) (n:nat) (t:RBTree c n), n <= depth min t.
Proof.
    intros c n t. 
    induction t as [|n t1 IH1 m t2 IH2|c1 c2 n t1 IH1 m t2 IH2].
    - apply le_n.
    - simpl. 
      destruct (min_dec (depth min t1) (depth min t2)) as [H|H]; 
      rewrite H; apply le_S; assumption.
    - simpl.
      destruct (min_dec (depth min t1) (depth min t2)) as [H|H]; 
      rewrite H; apply le_n_S; assumption.
Qed.

Lemma depth_max' : forall (c:Color) (n:nat) (t:RBTree c n),
    match c with
    | Red   => depth max t <= 2*n + 1
    | Black => depth max t <= 2*n
    end.
Proof.
    intros c n t.
    induction t as [|n t1 IH1 m t2 IH2|c1 c2 n t1 IH1 m t2 IH2].
    - apply le_n.
    - simpl. rewrite <- plus_n_Sm. apply le_n_S.
      rewrite <- plus_n_O, <- plus_n_O. rewrite plus_n_n.
      apply max_lub; assumption.
    - destruct c1 as [H1|H1], c2 as [H2|H2]. 
        + simpl. apply le_n_S. rewrite <- plus_n_O. rewrite <- plus_n_Sm.
          rewrite plus_n_n.
          rewrite <- plus_n_Sm in IH1. rewrite <- plus_n_O in IH1.
          rewrite <- plus_n_Sm in IH2. rewrite <- plus_n_O in IH2.
          apply max_lub; assumption.
        + simpl. apply le_n_S. rewrite <- plus_n_O. rewrite <- plus_n_Sm. 
          rewrite plus_n_n.
          rewrite <- plus_n_Sm in IH1. rewrite <- plus_n_O in IH1.
          apply max_lub.
            { assumption. }
            { apply le_S. assumption. }
        + simpl. apply le_n_S. rewrite <- plus_n_O. rewrite <- plus_n_Sm.
          rewrite plus_n_n.
          rewrite <- plus_n_Sm in IH2. rewrite <- plus_n_O in IH2.
          apply max_lub.
            { apply le_S. assumption. }
            { assumption. }
        + simpl. apply le_n_S. rewrite <- plus_n_O. rewrite <- plus_n_Sm.
          rewrite plus_n_n.
          apply max_lub; apply le_S; assumption.
Qed.

Theorem depth_max : forall (c:Color) (n:nat) (t:RBTree c n), 
    depth max t <= 2*n + 1.
Proof.
    intros c n t. destruct c as [H|H]. 
    - apply (depth_max' Red). 
    - rewrite <- plus_n_Sm. rewrite <- plus_n_O. apply le_S.
      apply (depth_max' Black).
Qed.


Theorem balanced : forall (c:Color) (n:nat) (t:RBTree c n), 
    depth max t <= 2 * (depth min t) + 1.
Proof.
    intros c n t. apply le_trans with (2 * n + 1).
    - apply depth_max.
    - apply plus_le_compat_r, mult_le_compat_l, depth_min.
Qed.


Inductive RTree : nat -> Set :=
| RedNode' : forall c1 c2 n, RBTree c1 n -> nat -> RBTree c2 n -> RTree n
.

Fixpoint present (c:Color) (n:nat) (t:RBTree c n) (x:nat) : Prop :=
    match t with
    | Leaf                      => False
    | RedNode _ t1 y t2         => present Black _ t1 x \/ y = x \/ present Black _ t2 x
    | BlackNode _ _ _ t1 y t2   => present _ _ t1 x \/ y = x \/ present _ _ t2 x
    end.

Arguments present {c} {n}.

Definition rpresent (n:nat) (t:RTree n) (x:nat) : Prop :=
    match t with
    | RedNode' _ _ _ t1 y t2    => present t1 x \/ y = x \/ present t2 x
    end.


Locate "_ :: _".
Locate "{ _ : _ & _ }".
Print sigT.

Notation "{< x >}" := (existT _ _ x).
