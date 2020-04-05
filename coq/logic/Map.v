Require Import List.

Require Import In.

Lemma mapIn : forall (v w:Type) (f:v -> w) (y:w) (xs:list v),
    y :: map f xs <-> exists (x:v), x :: xs /\ y = f x.
Proof.
    intros v w f y xs. split; intros H.
    - rewrite in_map_iff in H. destruct H as [x [H1 H2]].
      exists x. split.
        + assumption.
        + symmetry. assumption.
    - apply in_map_iff. destruct H as [x [H1 H2]].
      exists x. split.
        + symmetry. assumption.
        + assumption.
Qed.


