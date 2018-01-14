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
    intros a l. remember (length l) as n eqn:H.
    assert (length l <= n) as H'. { rewrite H. apply le_n. }
    clear H. revert H'. revert l. induction n as [|n IH].
    - intros l H1 H2. inversion H1. apply length_0_iff_nil in H0.
        rewrite H0. apply pal_empty.
    - intros l H1 H2.
Show.
*)
