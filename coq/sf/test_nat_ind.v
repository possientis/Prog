Require Import nat.
Require Import nat_ind.

Lemma test1 : forall (n:nat), n * 0 = 0.
Proof.
    apply nat_ind.
    - reflexivity.
    - intros n IH. simpl. exact IH.
Qed.

Definition test2 : forall (n:nat), n * 0 = 0 :=
    nat_ind (fun n => n * 0 = 0) (eq_refl 0) 
        (fun (n : nat) (IH: n * 0 = 0) => IH).


(* Show the proof *)
(*Print test1. *)
(*
test1 = 
nat_ind (fun n : nat => n * 0 = 0) eq_refl
  (fun (n : nat) (IH : n * 0 = 0) => IH)
       : forall n : nat, n * 0 = 0
*)


Lemma test3 : forall (n:nat), n + 1 = S n.
Proof.
    apply nat_ind.
    - reflexivity.
    - intros n IH. simpl. rewrite IH. reflexivity.
Qed.

Inductive yesno : Type :=
| yes : yesno
| no  : yesno
.

(*
Check yesno_ind.
*)

Lemma yesno_ind' : forall (P:yesno -> Prop), 
    P yes -> P no -> forall (x:yesno), P x.
Proof.
    intros P H1 H2 x. destruct x.
    - exact H1.
    - exact H2.
Qed.

