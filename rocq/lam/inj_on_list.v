Require Import List.
Import ListNotations.

Require Import injective.
Require Import incl.

Definition injective_on_list (v w:Type) (l:list v) (f:v -> w) : Prop :=
    forall (x y:v), In x l -> In y l -> f x = f y -> x = y.

Arguments injective_on_list {v} {w} _ _.

Lemma inj_is_inj_on_list : forall (v w:Type) (l:list v) (f:v-> w),
    injective f -> injective_on_list l f.
Proof.
    intros v w l f H. intros x y Hx Hy H'. apply H. assumption.
Qed.


Lemma injective_on_list_appl : forall (v w:Type) (l1 l2:list v) (f:v -> w),
    injective_on_list (l1 ++ l2) f -> injective_on_list l1 f.
Proof.
    intros v w l1 l2 f H x y Hx Hy H'.
    apply H; simpl.
    - apply in_or_app. left. assumption.
    - apply in_or_app. left. assumption.
    - assumption.
Qed.

Lemma injective_on_list_appr : forall (v w:Type) (l1 l2:list v) (f:v -> w),
    injective_on_list (l1 ++ l2) f -> injective_on_list l2 f.
Proof.
    intros v w l1 l2 f H x y Hx Hy H'.
    apply H; simpl.
    - apply in_or_app. right. assumption.
    - apply in_or_app. right. assumption.
    - assumption.
Qed.

Lemma injective_on_list_cons : forall (v w:Type) (a:v) (l:list v) (f:v -> w),
    injective_on_list (a :: l) f -> injective_on_list l f.
Proof.
    intros v w a l f H x y Hx Hy H'.
    apply H; simpl.
    - right. assumption.
    - right. assumption.
    - assumption.
Qed.

Lemma injective_incl : forall (v w:Type) (l l':list v) (f:v -> w),
    incl l l' -> injective_on_list l' f -> injective_on_list l f.
Proof.
    intros v w l l' f H0 H1 x y Hx Hy H. apply H1.
    - apply H0. assumption.
    - apply H0. assumption.
    - assumption.
Qed.


Lemma injective_not_in : forall (v w:Type) (f:v -> w),
    forall (x:v) (l:list v),
    injective_on_list (x :: l) f -> 
    ~In x l -> 
    ~In (f x) (map f l).
Proof.
    intros v w f x l. revert x. 
    induction l as [|a l IH]; simpl; intros x H.
    - intros H0 H1. assumption.
    - intros Hp [Hq|Hq].
        { apply Hp. left. apply H.
            { right. left. reflexivity. }
            { left. reflexivity. }
            { assumption. }
        }
        { revert Hq. apply IH.
            { apply injective_incl with (x :: a :: l).
                { apply incl_cons2. apply incl_tl. apply incl_refl. }
                { assumption. }
            }
            { intros H'. apply Hp. right. assumption. }
        }
Qed.


