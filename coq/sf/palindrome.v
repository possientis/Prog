Require Import list.

Inductive pal (a:Type) : list a -> Prop :=
| pal_empty : pal a []
| pal_sing  : forall (x:a), pal a [x]
| pal_ext   : forall (l:list a) (x:a), pal a l -> pal a (x :: l ++ [x]) 
.

Arguments pal {a} _.


Theorem pal_app_rev : forall (a:Type) (l:list a), pal (l ++ rev l).
Proof.
    intros a l. induction l as [|x xs IH].
    - apply pal_empty.
    - simpl. rewrite app_assoc. apply pal_ext. exact IH.
Qed.


Theorem pal_rev : forall (a:Type) (l:list a), pal l -> l = rev l.
Proof.
    intros a l H. induction H as [|x|xs x H IH].
    - reflexivity.
    - reflexivity.
    - simpl. rewrite rev_app_distr. rewrite <- IH. simpl. reflexivity.
Qed.

(*
Theorem pal_converse : forall (a:Type) (l:list a), l = rev l -> pal l.
Proof.
    intros a l. induction l as [|x xs IH].
    - intros _. apply pal_empty.
    - simpl. remember (rev xs) as l eqn:H.
        revert x. revert IH H. revert xs. induction l as [|y ys IH].
        + intros xs _ _ x H. rewrite H. apply pal_sing.
        + intros xs H0 H1 x H2. rewrite app_cons in H2.
            inversion H2. rewrite <- H3 at 1. rewrite <- H4. apply IH.
            { intros H5. remember (length xs) as n eqn:H6.
Show.
*)
