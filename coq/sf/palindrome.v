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

