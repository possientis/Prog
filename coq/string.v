Require Import String.

Open Scope string_scope.

Lemma L0 : "x" <> "y".
Proof.
    intros H. inversion H.
Qed.
