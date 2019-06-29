Require Import List.  
Require Import Eq.
Require Import Include.
Require Import Injective.

Lemma remove_still : forall (v:Type) (e:Eq v) (x y:v) (l:list v),
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
            { apply remove_still. 
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

Lemma remove_x_not_in : forall (v:Type) (e:Eq v) (x:v) (xs:list v),
    ~In x xs -> remove e x xs = xs.
Proof.
    intros v e x xs. induction xs as [|a xs IH]; simpl; intros H.
    - reflexivity.
    - destruct (e x a) as [Hx|Hx].
        + exfalso. apply H. left. symmetry. assumption.
        + rewrite IH.
            { reflexivity. }
            { intros H'. apply H. right. assumption. }
Qed.



Lemma remove_inj : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v)(xs:list v),
    In x xs -> 
    injective_on xs f -> 
    remove e' (f x) (map f xs) = map f (remove e x xs).
Proof.
    intros v w e e' f x xs. revert x.
    induction xs as [|a xs IH]; simpl; intros x Hx H.
    - reflexivity.
    - destruct (e' (f x) (f a)) as [Hq|Hq], (e x a) as [Hp|Hp].
        + destruct (in_dec e x xs) as [Hl|Hl].
            { apply IH.
                { assumption. }
                { apply injective_on_cons with a. assumption. }
            }
            { assert (remove e x xs = xs) as P. 
                { apply remove_x_not_in. assumption. }
                rewrite P.
                apply remove_x_not_in.
                apply injective_on_not_in.
                    { rewrite Hp. assumption. }
                    { assumption. }
            }
        + exfalso. apply Hp. apply H.
            { assumption. }
            { left. reflexivity. }
            { assumption. }
        + exfalso. apply Hq. rewrite Hp. reflexivity.
        + simpl. destruct Hx as [Hx|Hx].
            { exfalso. apply Hp. symmetry. assumption. }
            { rewrite IH.
                { reflexivity. }
                { assumption. }
                { apply injective_on_incl with (a :: xs).
                    { apply incl_tl. apply incl_refl. }
                    { assumption. } 
                }
            }
Qed.

Lemma remove_inj2 : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v)(xs:list v),
    injective_on (x :: xs) f -> 
    remove e' (f x) (map f xs) = map f (remove e x xs).
Proof.
    intros v w e e' f x xs H.
    assert 
        (remove e' (f x) (map f (x :: xs)) = map f (remove e x (x :: xs))) as E.
        { apply remove_inj.
            - left. reflexivity.
            - assumption.
        }
    simpl in E.
    destruct (e x x) as [Hp|Hp], (e' (f x) (f x)) as [Hq|Hq].
    - assumption.
    - exfalso. apply Hq. reflexivity.
    - exfalso. apply Hp. reflexivity.
    - inversion E. reflexivity.
Qed.

Lemma remove_incl : forall (v:Type) (e:Eq v) (x:v) (xs:list v), 
    incl (remove e x xs) xs. 
Proof.
    intros v e x xs. induction xs as [|a xs IH]; simpl.
    - apply incl_refl.
    - destruct (e x a) as [H|H].
        + apply incl_tl. assumption.
        + apply incl_cons2. assumption.
Qed.

