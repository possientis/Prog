Require Import Omega.

Open Scope Z_scope.

Lemma L1: forall (n m:Z), 1 + 2 * m <> 2 * n.
Proof.
    intros n m. omega.
Qed.


Lemma L2: forall (z:Z), z > 0 -> 2 * z + 1 > z.
Proof. intros z. omega. Qed.

