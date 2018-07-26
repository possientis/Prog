Require Import List.
Import ListNotations.

Require Import eq.
Require Import incl.
Require Import injective.



Lemma remove_In2 : forall (v:Type) (p:Eq v) (x y:v) (l:list v),
    x <> y -> In y l -> In y (remove p x l).
Proof.
    intros v p x y l. induction l as [|a l IH].
    - intros _ H. inversion H.
    - intros Exy H. simpl. destruct (p x a) eqn:Exa. 
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

Lemma remove_mon : forall (v:Type) (p:Eq v) (x:v) (l l':list v),
    incl l l' -> incl (remove p x l) (remove p x l').
Proof.
    intros v p x l. induction l as [|a l IH]; simpl; intros l' H.
    - intros y Hy. inversion Hy.
    - destruct (p x a) eqn:E.
        + apply IH. intros y Hy. apply H. right. assumption.
        + intros y Hy. destruct (p y a) as [H1|H2].
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

Lemma remove_map : forall (v w:Type) (p:Eq v) (q:Eq w) (f:v -> w) (x:v) (l:list v),
    incl (remove q (f x) (map f l)) (map f (remove p x l)).
Proof.
    intros v w p q f x l. induction l as [|a l IH]; simpl.
    - apply incl_refl.
    - destruct (p x a) as [P|P].
        + destruct (q (f x) (f a)) as [Q|Q].
            { assumption. }
            { exfalso. apply Q. rewrite P. reflexivity. }
        + destruct (q (f x) (f a)) as [Q|Q].
            { apply incl_tl. assumption. }
            { simpl. intros y Hy. destruct Hy.
                { left. assumption. }
                { right. apply IH. assumption. }
            }
Qed.



Lemma remove_incl : forall (v:Type) (p:Eq v) (x:v) (l:list v), 
    incl (remove p x l) l. 
Proof.
    intros v p x l. induction l as [|a l IH]; simpl.
    - apply incl_refl.
    - destruct (p x a) as [H|H].
        + apply incl_tl. assumption.
        + apply incl_cons2. assumption.
Qed.

Lemma remove_x_not_in : forall (v:Type) (p:Eq v) (x:v) (l:list v),
    ~In x l -> remove p x l = l.
Proof.
    intros v p x l. induction l as [|a l IH]; simpl; intros H.
    - reflexivity.
    - destruct (p x a) as [Hx|Hx].
        + exfalso. apply H. left. symmetry. assumption.
        + rewrite IH.
            { reflexivity. }
            { intros H'. apply H. right. assumption. }
Qed.



Lemma remove_inj : forall (v w:Type) (p:Eq v) (q:Eq w) (f:v -> w) (x:v) (l:list v),
    In x l -> 
    injective_on_list l f -> 
    remove q (f x) (map f l) = map f (remove p x l).
Proof.
    intros v w p q f x l. revert x.
    induction l as [|a l IH]; simpl; intros x Hx H.
    - reflexivity.
    - destruct (q (f x) (f a)) as [Hq|Hq], (p x a) as [Hp|Hp].
        + destruct (in_dec p x l) as [Hl|Hl].
            { apply IH.
                { assumption. }
                { apply injective_on_list_cons with a. assumption. }
            }
            { assert (remove p x l = l) as P. 
                { apply remove_x_not_in. assumption. }
                rewrite P.
                apply remove_x_not_in.
                apply injective_not_in.
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
                { apply injective_incl with (a :: l).
                    { apply incl_tl. apply incl_refl. }
                    { assumption. } 
                }
            }
Qed.

Lemma remove_inj2 : forall (v w:Type) (p:Eq v) (q:Eq w) (f:v -> w) (x:v) (l:list v),
    injective_on_list (x :: l) f -> 
    remove q (f x) (map f l) = map f (remove p x l).
Proof.
    intros v w p q f x l H.
    assert (remove q (f x) (map f (x :: l)) = map f (remove p x (x :: l))) as E.
        { apply remove_inj.
            - left. reflexivity.
            - assumption.
        }
    simpl in E.
    destruct (p x x) as [Hp|Hp], (q (f x) (f x)) as [Hq|Hq].
    - assumption.
    - exfalso. apply Hq. reflexivity.
    - exfalso. apply Hp. reflexivity.
    - inversion E. reflexivity.
Qed.

