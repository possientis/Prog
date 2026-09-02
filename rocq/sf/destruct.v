Require Import nat.
Require Import bool.

Definition sillyfun (n:nat) : bool :=
    if eqb n 3 then false
        else if eqb n 5 then false
            else false.

Theorem sillyfun_false : forall (n:nat),
    sillyfun n = false.
Proof.
    intros n. unfold sillyfun.
    destruct (eqb n 3).
    - reflexivity.
    - destruct (eqb n 5).
        +  reflexivity.
        +  reflexivity.
Qed.


Definition sillyfun1 (n:nat) : bool :=
    if eqb n 3 then true
        else if eqb n 5 then true
            else false.

Theorem sillyfun1_odd : forall (n:nat),
    sillyfun1 n = true -> oddb n = true.
Proof.
    intros n H. unfold sillyfun1 in H.
    destruct (eqb n 3) eqn:H3.  (* cool !!!!!! *)
    - apply eqb_semantics in H3. rewrite H3. reflexivity.
    - destruct (eqb n 5) eqn:H5. (* cool !!!!! *)
        + apply eqb_semantics in H5. rewrite H5. reflexivity.
        + inversion H.
Qed.

Theorem bool_fn_applied_thrice : forall (f:bool -> bool) (b:bool),
    f (f (f b)) = f b.
Proof.
    intros f. destruct b, (f true) eqn:H1, (f false) eqn:H2.
    -  rewrite H1, H1. reflexivity.
    -  rewrite H1, H1. reflexivity.
    -  exact H1.
    -  exact H2.
    -  rewrite H1, H1. reflexivity.
    -  rewrite H2, H2. reflexivity.
    -  rewrite H1, H2. reflexivity.
    -  rewrite H2, H2. reflexivity.
Qed.


