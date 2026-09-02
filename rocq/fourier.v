Require Import Reals.
Require Import Fourier.

Theorem example_for_fourier : forall x y:R, x-y>1 -> x-2*y<0-> y>1.
Proof.
  intros x y H H'. fourier.
Qed.
