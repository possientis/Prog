Require Import List.

Require Import Utils.Eq.
Require Import Utils.Equiv.

(* Removes duplicates from the list xs.                                         *)
Fixpoint nub (a:Type) (e:Eq a) (xs:list a) : list a :=
    match xs with
    | nil       => nil
    | cons y ys =>
        match (in_dec eqDec y ys) with
        | left _    => nub a e ys
        | right _   => cons y (nub a e ys)
        end
    end.

Arguments nub {a} {e}.

(* Whether a list has no duplicate: need usual equality but not Eq instance.    *)
Inductive Nubed (a:Type) : list a -> Prop :=
| NubedNil    : Nubed a nil
| NubedCons   : forall (x:a) (xs:list a),
    ~In x xs -> Nubed a xs -> Nubed a (cons x xs)
.

Arguments Nubed     {a}.
Arguments NubedNil  {a}.
Arguments NubedCons {a}.

(* Nubing preserves the elements of a list.                                     *)
Lemma nubInIff : forall (a:Type) (e:Eq a) (x:a) (xs:list a),
    In x xs <-> In x (nub xs).
Proof.
    intros a e x xs. revert x. induction xs as [|x xs IH];
    intros y; simpl; split; intros H.
    - contradiction.
    - contradiction.
    - destruct H as [H1|H1]; destruct (in_dec eqDec x xs) as [H2|H2].
        + subst. apply IH. assumption.
        + subst. left. reflexivity.
        + apply IH. assumption.
        + right. apply IH. assumption.
    - destruct (in_dec eqDec x xs) as [H1|H1].
        + right. apply IH. assumption.
        + destruct H as [H|H].
            { left. assumption. }
            { right. apply IH. assumption. }
Qed.

Lemma nubEquiv : forall (a:Type) (e:Eq a) (xs:list a), Equiv xs (nub xs).
Proof.
    intros a e xs. split; intros x H.
    - apply nubInIff. assumption.
    - rewrite nubInIff. exact H. (* 'assumption' fails, why ?                      *)
Qed.

(* Nubing a list leads to a Nubed list.                                         *)
Lemma nubNubed : forall (a:Type) (e:Eq a) (xs:list a), Nubed (nub xs).
Proof.
    intros a e. induction xs as [|x xs IH]; simpl.
    - constructor.
    - destruct (in_dec eqDec x xs) as [H|H].
        + assumption.
        + constructor.
            (* assumption tactic fails to work here. Very bizarre -> exact.     *)
            { intros H1. apply H. rewrite nubInIff. exact H1. }
            { assumption. }
Qed.

Lemma nubSame : forall (a:Type) (e:Eq a) (xs:list a), 
    Nubed xs -> nub xs = xs.
Proof.
    intros a e xs H. induction H as [|x xs H1 H2 IH].
    - reflexivity.
    - simpl. destruct (in_dec eqDec x xs) as [H3|H3].
        + apply H1 in H3. contradiction.
        + rewrite IH. reflexivity.
Qed.

Lemma nubedConsNotIn : forall (a:Type) (e:Eq a) (x:a) (xs:list a),
    Nubed (cons x xs) -> ~ In x xs.
Proof.
    intros a e x xs H. remember (cons x xs) as ys eqn:E. 
    revert E. revert xs. revert x. destruct H; intros y ys H1.
    - inversion H1.
    - inversion H1. subst. assumption.
Qed.

Lemma nubedConsNubedTail : forall (a:Type) (e:Eq a) (x:a) (xs:list a),
    Nubed (cons x xs) -> Nubed xs.
Proof.
    intros a e x xs H. remember (cons x xs) as ys eqn:E.
    revert E. revert x xs. destruct H as [|x xs H1 H2]; intros z zs H.
    - inversion H.
    - inversion H. subst. assumption.
Qed.
