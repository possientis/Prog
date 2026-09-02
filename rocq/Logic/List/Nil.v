Require Import List.

Require Import Logic.List.In.

Lemma nil_charac : forall (v:Type) (xs:list v),
    xs = nil <-> forall (x:v), ~ (x::xs). 
Proof.
    intros v xs. split; intros H1.
    - intros x H2. destruct xs as [|x' xs].
        + inversion H2.
        + inversion H1.
    - destruct xs as [|x' xs].
        + reflexivity.
        + exfalso. apply (H1 x'). left. reflexivity.
Qed.

(* A list is not empty if and only if it has an element which lies in it.       *)
Lemma nil_exists : forall (a:Type) (xs:list a),
    (exists (x:a), In x xs) <-> xs <> nil.
Proof.
    intros a xs. destruct xs as [|x xs]; split.
    - intros [x H]. inversion H.
    - intros H. exfalso. apply H. reflexivity.
    - intros H1 H2. inversion H2.
    - intros H. exists x. left. reflexivity.
Qed.

(* Whether a list is the empty list or not is decidable.                        *)
Lemma nil_Dec : forall (a:Type) (xs:list a), {xs = nil} + {xs <> nil}.
Proof.
    intros a xs. destruct xs as [|x xs].
    - left. reflexivity.
    - right. intros H. inversion H.
Qed.


Arguments nil_Dec {a}.


