Require Import Arith.

Fixpoint fib1 (n:nat) : nat :=
  match n with
    | 0       => 1
    | S p     => match p with
                  | 0     => 1
                  | S m   => fib1 p + fib1 m
                end
  end.

(*
Eval compute in fib1 22.
*)

Fixpoint fib2 (n:nat) : nat*nat :=
  match n with
    | 0       =>  (1,1)
    | S p     =>  let v := fib2 p in 
                    (fst v + snd v, fst v)
  end. 

(*
Eval compute in (snd (fib2 22)).
*)

Lemma fib_eq : forall (n:nat), fib2 n = (fib1 (S n), fib1 n).
Proof.
  induction n. simpl. reflexivity. 
  unfold fib2. fold fib2. rewrite IHn. unfold fst. unfold snd.
  set (a:= fib1 (S n)). set (b:= fib1 n). unfold fib1. fold fib1.
  fold b. change ((a + b, a) = (a + b, a)). reflexivity.
Qed. 

Theorem nat_2_ind: forall P:nat->Prop,
  P 0 -> P 1 -> (forall n:nat, P n -> P (S n) -> P (S (S n))) -> forall n:nat, P n.
Proof.
  intros P H0 H1 IH n. cut (P n /\ P (S n)). tauto. elim n; intuition.
  (*
  clear n. split; assumption.
  clear n. intros n [H2 H3]. split. exact H3. apply IH. exact H2.
  *)
Qed.

Theorem exercise: forall n p: nat,
  fib1 (S (S (n + p))) = fib1 (S n) * fib1 (S p) + fib1 n * fib1 p.
Proof.
  intros n p. pattern n. apply nat_2_ind.
  simpl. auto. 
  simpl. rewrite plus_0_r, plus_0_r. rewrite plus_assoc_reverse.
  rewrite plus_comm with (n:=fib1 p). rewrite plus_assoc. reflexivity.
  clear n. intros n H0 H1. set (a:= fib1 (S p)). set (b := fib1 p).
  fold a in H0. fold b in H0. fold a in H1. fold b in H1.
  cut (fib1 (S (S (S (S n) + p))) = fib1 (S (S (S n + p))) + fib1 (S (S (n + p)))). 
  cut (fib1 (S (S (S n))) = fib1 (S (S n)) + fib1 (S n)).
  cut (fib1 (S (S n)) = fib1 (S n) + fib1 n).
  intros H2 H3 H4. rewrite H4. rewrite H1, H0. rewrite plus_assoc_reverse.
  rewrite plus_assoc with (n:= fib1 (S n) * b).
  rewrite plus_comm with (n:= fib1 (S n)* b). rewrite plus_assoc_reverse.
  rewrite plus_assoc. 
  rewrite <- mult_plus_distr_r with (p:=a).
  rewrite <- mult_plus_distr_r with (p:=b).
  rewrite <- H2, H3. reflexivity.
  simpl. reflexivity. 
  simpl. reflexivity.
  rewrite plus_Snm_nSm. rewrite <- plus_n_Sm. 
  rewrite plus_Snm_nSm. rewrite <- plus_n_Sm.
  set (q:= S (S (n+p))). unfold fib1. fold fib1. reflexivity.
Qed.

Lemma obvious: forall n:nat,
  fib1 (S (S n)) = fib1 (S n) + fib1 n.
Proof.
  intro n. unfold fib1. fold fib1. reflexivity.
Qed.


