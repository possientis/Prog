Require Import list.
Require Import In.


Definition disjoint (a:Type) (l k:list a) : Prop :=
    forall x, In x l -> In x k -> False.

Arguments disjoint {a} _ _.

Inductive nodup (a:Type) : list a -> Prop :=
| nodup_nil  : nodup a []
| nodup_cons : forall (l:list a) (x:a), nodup a l -> ~In x l -> nodup a (x :: l)
.

Arguments nodup {a} _.

Theorem app_nodup_disjoint : forall (a:Type) (l k:list a),
    nodup l -> nodup k -> disjoint l k -> nodup (l ++ k).
Proof.
    intros a l k H. revert k. induction H as [|l x H1 IH1 H2].
    - intros k H _. exact H.
    - intros k H. induction H as [|k y H1' IH1' H2'].
        + intros _. rewrite app_nil_r. apply nodup_cons.
            { exact H1. }
            { exact H2. }
        + intros H. rewrite app_cons. apply nodup_cons.
            { apply IH1.
                { apply nodup_cons.
                    { exact H1'. }
                    { exact H2'. }
                }
                { unfold disjoint. intros z Hz Hz'.  unfold disjoint in H.
                    apply (H z).
                        { right. exact Hz. }
                        { exact Hz'. }
                }
            }
            { intros H'. rewrite In_app_iff in H'. destruct H' as [H'|H'].
                { apply H2. exact H'. }
                { simpl in H'. destruct H' as [H'|H'].
                    { unfold disjoint in H. apply (H x).
                        { left. reflexivity. }
                        { left. exact H'. }
                    }
                    { unfold disjoint in H. apply (H x).
                        { left. reflexivity. }
                        { right. exact H'. }
                    }
                }
            }
Qed.


Inductive nostutter (a:Type) : list a -> Prop :=
| nostutter_nil     : nostutter a []
| nostutter_single  : forall (x:a), nostutter a [x]
| nostutter_double  : forall (x y:a) (l:list a), 
    nostutter a (x :: l) -> x <> y -> nostutter a (y :: x :: l)
.

Arguments nostutter {a} _.

Inductive repeats (a:Type): list a -> Prop :=
| repeat_In   : forall (x:a) (xs:list a), In x xs -> repeats a (x :: xs)
| repeat_cons : forall (x:a) (xs:list a), repeats a xs -> repeats a (x :: xs)
.

Arguments repeats {a} _.

Theorem nodup_iff_not_repeats : forall (a:Type) (l:list a),
    nodup l <-> ~ repeats l.
Proof.
    intros a l. split.
    - intros H. induction H as [|l x H1 IH1 H2].
        + intros H. inversion H.
        + intros H'. remember (x :: l) as k eqn:Hk.
        revert Hk H2 IH1. induction H' as [y xs H2|y xs H2 IH2].
        { intros H3 H4 H5. apply H4. inversion H3 as [H6].
            rewrite H6 in H2. rewrite H in H2. exact H2. 
        }
        { intros H3 H4 H5. apply H5. inversion H3 as [H6].
            rewrite H in H2. exact H2.
        }
    - induction l as [|x xs IH]. 
        + intros _. apply nodup_nil.
        + intros H. apply nodup_cons.
            { apply IH. intros H'. apply H. apply repeat_cons. exact H'. }
            { intros H'. apply H. apply repeat_In. exact H'. }
Qed.

(*
Theorem repeats_iff_not_nodup : forall (a:Type) (l:list a),
    repeats l <-> ~ nodup l.
Proof.
    intros a l. split.
    - intros H. induction H as [x xs H|x xs H IH].
        + intros H'. remember (x :: xs) as l eqn:Hl.
            revert H Hl. induction H' as [|l y H1 IH1 H2].
            { intros H1 H2. inversion H2. }
            { intros H3 H4.

Show.
*)

