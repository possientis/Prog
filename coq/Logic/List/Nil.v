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

