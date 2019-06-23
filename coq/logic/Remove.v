Require Import List.

Require Import Eq.

Lemma remove_In2 : forall (v:Type) (e:Eq v) (x y:v) (l:list v),
    x <> y -> In y l -> In y (remove e x l).
Proof.
    intros v e x y l. induction l as [|a l IH].
    - intros _ H. inversion H.
    - intros Exy H. simpl. destruct (e x a) eqn:Exa. 
        + apply IH.
            { assumption. }
            { destruct H as [H1|H2]. 
                { exfalso. apply Exy. rewrite <- H1. assumption. }
                { assumption. }
            }
        + destruct H.  
            { left. assumption. }
            { right. apply IH; assumption. }
Qed.


Lemma remove_mon : forall (v:Type) (e:Eq v) (x:v) (l l':list v),
    incl l l' -> incl (remove e x l) (remove e x l').
Proof.
    intros v e x l. induction l as [|a l IH]; simpl; intros l' H.
    - intros y Hy. inversion Hy.
    - destruct (e x a) eqn:E.
        + apply IH. intros y Hy. apply H. right. assumption.
        + intros y Hy. destruct (e y a) as [H1|H2].
            { apply remove_In2. 
                { rewrite H1. assumption. }
                { apply H. left. symmetry. assumption. }
            }
            { apply IH.
                { intros z Hz. apply H. right. assumption. }
                { destruct Hy as [G1|G2].
                    { exfalso. apply H2. symmetry. assumption. }
                    { assumption. }
                 }
            }
Qed.

Lemma remove_map : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v) (xs:list v),
    incl (remove e' (f x) (map f xs)) (map f (remove e x xs)).
Proof.
    intros v w e e' f x xs. induction xs as [|a xs IH]; simpl.
    - apply incl_refl.
    - destruct (e x a) as [P|P].
        + destruct (e' (f x) (f a)) as [Q|Q].
            { assumption. }
            { exfalso. apply Q. rewrite P. reflexivity. }
        + destruct (e' (f x) (f a)) as [Q|Q].
            { apply incl_tl. assumption. }
            { simpl. intros y Hy. destruct Hy.
                { left. assumption. }
                { right. apply IH. assumption. }
            }
Qed.


