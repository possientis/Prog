Require Import nat.
Require Import le.
Require Import list.
Require Import In.

Inductive repeats (a:Type): list a -> Prop :=
| repeat_In   : forall (x:a) (xs:list a), In x xs -> repeats a (x :: xs)
| repeat_cons : forall (x:a) (xs:list a), repeats a xs -> repeats a (x :: xs)
.

Arguments repeats {a} _.

Theorem pigeon_hole_with_LEM : forall (a:Type)(l k:list a),
    (forall (x y:a), x = y \/ x <> y) ->
    (forall x, In x l -> In x k) ->
    length k < length l ->
    repeats l.
Proof.
    intros a l k EqDec I L.
    assert (forall (x:a) (l:list a), In x l \/ ~In x l) as InDec.
    { apply In_Decidable. exact EqDec. } clear EqDec.
    revert I. revert L. revert k. induction l as [|x xs IH]. 
    - intros k H. inversion H.
    - intros k L I. destruct (InDec x xs) as [Hx|Hx]. 
        + apply repeat_In. exact Hx.
        + apply repeat_cons.
            assert (exists k1 k2, k = k1 ++ x :: k2) as [k1 [k2 H0]].
            { apply In_split. apply I. left. reflexivity. }
            apply (IH (k1++k2)).
                { apply Sn_lt_Sm__n_lt_m. rewrite app_length.
                    rewrite H0 in L. rewrite app_length in L.
                    simpl in L. rewrite plus_n_Sm in L. exact L.
                }
                { intros y Hy. 
                    assert (y <> x) as Exy.
                        { intros E. apply Hx. rewrite <- E. exact Hy. }
                    assert (In y k) as Iyk. 
                        { apply I. right. exact Hy. }
                    rewrite H0 in Iyk. rewrite In_app_iff.
                    rewrite In_app_iff in Iyk. destruct Iyk as [H1|[H1|H1]]. 
                        { left. exact H1. }
                        { exfalso. apply Exy. symmetry. exact H1. }
                        { right. exact H1. }
                }
Qed.

(*
Lemma temp : forall (a:Type) (l k:list a) (x:a),
    In x k -> length l = length k -> (forall u, In u l -> In u k) -> 
    repeats (x :: l).
Proof.


Show.
*)
           

 (*
Theorem pigeon_hole : forall (a:Type) (l k:list a),
    (forall x, In x l -> In x k) ->
    length k < length l ->
    repeats l.
Proof.
    intros a l. induction l as [|x xs IHl].
    - intros k H H'. inversion H'.
    - intros k. revert IHl. revert xs x. induction k as [|y ys IHk].
        + intros xs x IHl H. assert (In x []) as H'.
            { apply H. left. reflexivity. }
            inversion H'.
        + intros xs x H H' L. assert (In x (y::ys)) as H0.
            { apply H'. left. reflexivity. }
            destruct H0 as [H0|H0].
                { 
Show.
*)



