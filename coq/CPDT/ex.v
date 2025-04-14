Require Import Arith.Le.

Print ex.

(*
Inductive ex (a : Type) (P : a -> Prop) : Prop :=
| ex_intro : forall x : a, P x -> exists y, P y
*)

Inductive ex2 (a:Type) (P:a -> Prop) : Prop :=
| ex2_intro : forall (x:a), P x -> ex2 a P
.

Arguments ex2 {a} _.
Arguments ex2_intro {a} {P} _ _.

(* there exists n:nat, n + 3 = 5 *)
Lemma test1 : ex2 (fun (n:nat) => n + 3 = 5).
Proof. apply ex2_intro with 2. reflexivity. Qed.

Check ex2_intro.

Lemma test2 : ex2 (fun (n:nat) => n + 3 = 5).
Proof. apply (ex2_intro 2). reflexivity. Qed.


Lemma exist1 : exists (n:nat), n + 3 = 5.
Proof. exists 2. reflexivity. Qed.

Lemma exist2 : forall (n m:nat), (exists (p:nat), n + p = m) -> n <= m.
Proof.
    intros n m [p H]. revert p n m H. induction p as [|p IH]; intros n m.
    - intros H. rewrite <- plus_n_O in H. rewrite H. constructor.
    - intros H. apply le_trans with (S n).
        + constructor. constructor.
        + apply IH. simpl. rewrite <- plus_n_Sm in H. assumption.
Qed.


