Require Import le.
Require Import nat.
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

Theorem pal_converse : forall (a:Type) (l:list a), l = rev l -> pal l.
Proof.
    intros a l. remember (length l) as n eqn:H.
    assert (length l <= n) as H'. { rewrite H. apply le_n. }
    clear H. revert H'. revert l. induction n as [|n IH].
    - intros l H1 H2. inversion H1. apply length_0_iff_nil in H0.
        rewrite H0. apply pal_empty.
    - intros l H1 H2. apply (rev_list_3_cases a l) in H2.
        destruct H2 as [H2|[[x H2]|[x [k [H2 H3]]]]].
        + rewrite H2. apply pal_empty.
        + rewrite H2. apply pal_sing.
        + rewrite H2. apply pal_ext. apply IH. 
        { assert (S (S (length k)) = length l) as H4.
            { rewrite H2. simpl. rewrite app_length. simpl.
                rewrite <- plus_n_Sm. rewrite plus_n_0. reflexivity.
            }

            apply le_trans with (m:= S (length k)).
                { apply le_S, le_n. }
                { apply Sn_le_Sm__n_le_m. rewrite H4. exact H1. }
        }
        { exact H3. }
Qed.
