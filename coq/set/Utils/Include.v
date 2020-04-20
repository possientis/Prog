Require Import List.

Lemma inclNil : forall (a:Type) (xs:list a), incl xs nil -> xs = nil.
Proof.
    intros a. destruct xs as [|x xs]; intros H.
    - reflexivity.
    - exfalso. destruct (H x). left. reflexivity.
Qed.
