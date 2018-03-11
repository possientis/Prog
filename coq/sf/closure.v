Require Import nat.
Require Import le.

Definition relation (a:Type) : Type := a -> a -> Prop.

Inductive clos (a:Type) (r:relation a) : relation a :=
| rt_step : forall x y, r x y -> clos a r x y
| rt_refl : forall x, clos a r x x
| rt_trans: forall x y z, clos a r x y -> clos a r y z -> clos a r x z
.

Arguments clos {a} _.

Inductive next : relation nat := nextS : forall n, next n (S n).

(* '<=' is the reflexive-transitive closure of 'next' *)

Lemma le_is_clos_next : forall (n m:nat), n <= m <-> clos next n m.
Proof.
    intros n m . split.
    - intros H. induction H as [n|n m H IH].
        + apply rt_refl.
        + apply rt_trans with (y:=m).
            { exact IH. }
            { apply rt_step, nextS. }
    - intros H. induction H as [n m H|n|n m p H1 IH1 H2 IH2].
        + inversion H. apply le_S, le_n.
        + apply le_n.
        + apply le_trans with (m:=m).
            { exact IH1. }
            { exact IH2. }
Qed.

(*  The definition of refl-trans closure not very convenient
    for doing proofs, due to the 'non-determinism' of the 
    transitive rule. We are now trying a more useful definition. 
*)


Inductive clos' (a:Type) (r:relation a) (x:a) : a -> Prop :=
| rt'_refl : clos' a r x x
| rt'_mix  : forall (y z:a), r x y -> clos' a r y z -> clos' a r x z
.

Arguments clos' {a} _ _ _.

(* are these two definitions equivalent *)

Lemma rt'_step : forall (a:Type) (r:relation a) (x y:a), 
    r x y -> clos' r x y.
Proof.
    intros a r x y H. apply rt'_mix with (y:=y). 
    - exact H.
    - apply rt'_refl.
Qed.

Lemma rt'_trans : forall (a:Type) (r:relation a) (x y z:a),
    clos' r x y -> clos' r y z -> clos' r x z.
Proof.
    intros a r x y z H. revert z. induction H as [|x y z Hxy H IH].
    - intros z H. exact H.
    - intros z' H'. apply rt'_mix with (y:=y).
        + exact Hxy.
        + apply IH. exact H'.
Qed.

Lemma clos_iff_clos' : forall (a:Type) (r: relation a) (x y:a),
    clos r x y <-> clos' r x y.
Proof.
    intros a r x y. split.
    - intros H. induction H as [x y H|x|x y z H1 IH1 H2 IH2].
        + apply rt'_step. exact H.
        + apply rt'_refl.
        + apply rt'_trans with (y:=y).
            { exact IH1. }
            { exact IH2. }
    - intros H. induction H as [x|x y z H H' IH'].
        + apply rt_refl.
        + apply rt_trans with (y:=y).
            { apply rt_step. exact H. }
            { exact IH'. }
Qed.

