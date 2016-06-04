
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
  simpl. 
  


