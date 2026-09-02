Require Import Sets.Integers.

Lemma weaken_r : forall (x y y' n:nat),
    (x + y' <= n) -> (y <= y') -> x + y <= n.
Proof.
    intros x y y' n H1 H2.
    apply le_trans with (x + y').
    - apply Nat.add_le_mono_l. assumption.
    - assumption.
Qed.

Lemma weaken_l : forall (x x' y n:nat),
    (x' + y <= n) -> (x <= x') -> x + y <= n.
Proof.
    intros x x' y n H1 H2.
    apply le_trans with (x' + y).
    - apply Nat.add_le_mono_r. assumption.
    - assumption.
Qed.

Lemma weaken_l' : forall (x x' y n:nat),
    (x' + y <= S n) -> (S x <= x') -> x + y <= n.
Proof.
    intros x x' y n H1 H2. apply le_S_n.
    apply le_trans with (x' + y).
    - apply (Nat.add_le_mono_r (S x) x' y). assumption.
    - assumption.
Qed.

Lemma weaken3_l : forall (x x' y z n:nat),
    (x' + y + z <= n) -> (x <= x') -> x + y + z <= n.
Proof.
    intros x x' y z n H1 H2. apply weaken_l with (x' + y).
    - assumption.
    - apply Nat.add_le_mono_r. assumption.
Qed.

Lemma weaken3_m : forall (x y y' z n:nat),
    (x + y' + z <= n) -> (y <= y') -> x + y + z <= n.
Proof.
    intros x y y' z n H1 H2. apply weaken_l with (x + y').
    - assumption.
    - apply Nat.add_le_mono_l. assumption.
Qed.

