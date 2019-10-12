Require Import Nat.
Require Import Min.
Require Import Max.
Require Import Plus.

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

(*
Check min_dec.
*)

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

(*
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

Show.
*)

(*
Theorem depth_max : forall (c:Color) (n:nat) (t:RBTree c n), 
    depth max t <= 2*n + 1.
Proof.
    intros c n t.
    induction t as [|n t1 IH1 m t2 IH2|c1 c2 n t1 IH1 m t2 IH2].
    - apply le_S, le_n.
    - simpl.
Show.
*)
