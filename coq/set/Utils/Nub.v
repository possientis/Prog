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

(* Nubing preserves the elements of a list.                                     *)
Lemma nubPreserve : forall (a:Type) (e:Eq a) (x:a) (xs:list a),
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

(* Whether a list has no duplicate: need usual equality but not Eq instance.    *)
Inductive Nubed (a:Type) : list a -> Prop :=
| NubedNil    : Nubed a nil
| NubedCons   : forall (x:a) (xs:list a),
    ~In x xs -> Nubed a xs -> Nubed a (cons x xs)
.

Arguments Nubed     {a}.
Arguments NubedNil  {a}.
Arguments NubedCons {a}.

(* Nubing a list leads to a Nubed list.                                         *)
Lemma nubNubed : forall (a:Type) (e:Eq a) (xs:list a), Nubed (nub xs).
Proof.
    intros a e. induction xs as [|x xs IH]; simpl.
    - constructor.
    - destruct (in_dec eqDec x xs) as [H|H].
        + assumption.
        + constructor.
            (* assumption tactic fails to work here. Very bizarre -> exact.     *)
            { intros H1. apply H. rewrite nubPreserve. exact H1. }
            { assumption. }
Qed.


(*
Lemma nubEquiv : forall (a:Type) (e:Eq a) (xs:list a), Equiv xs (nub xs).
Proof.

Show.
*)
