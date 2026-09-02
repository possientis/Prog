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


Inductive rgb : Type := 
| red   : rgb
| green : rgb 
| blue  : rgb
.

(*
Check rgb_ind.
*)

Inductive natlist : Type := 
| nnil  : natlist
| ncons : nat -> natlist -> natlist
.

(*
Check natlist_ind.
*)

Inductive natlist' : Type := 
| nnil' : natlist'
| ncons': natlist' -> nat -> natlist'
.

(*
Check natlist'_ind.
*)

Inductive byntree : Type :=
| bempty : byntree
| bleaf  : yesno -> byntree
| bnode  : yesno -> byntree -> byntree -> byntree
.

Definition byntree_ind'_principle : Prop :=
    forall (P:byntree -> Prop),
        P bempty                                    ->
        (forall (b:yesno), P (bleaf b))             ->
        (forall (b:yesno) (t1 t2:byntree),
            P t1 -> P t2 -> P (bnode b t1 t2))      ->
        forall (t:byntree), P t.



(* obtained from 'Check byntree_ind' after variable renaming *)

Definition byntree_ind_principle : Prop :=
    forall (P : byntree -> Prop),
        P bempty                                    ->
        (forall (b:yesno), P (bleaf b))             ->
        (forall (b:yesno) (t1:byntree), P t1 -> 
            forall (t2:byntree), P t2        -> 
                P (bnode b t1 t2))                  ->
        forall (t:byntree), P t.





(* proving correctness of our hand made inductive principle *)

Lemma test4 : byntree_ind'_principle <-> byntree_ind_principle.
Proof.
    unfold byntree_ind'_principle, byntree_ind_principle. split.
    - intros H P H0 H1 H2 t. apply H.
        + exact H0.
        + exact H1.
        + intros b t1 t2 P1 P2. apply H2.
            { exact P1. }
            { exact P2. }
    - intros H P H0 H1 H2 t. apply H.
        + exact H0.
        + exact H1.
        + intros b t1 P1 t2 P2. apply H2.
            { exact P1. }
            { exact P2. }
Qed.


(* The proof of our hand made induction principle is also done 
   manually using recursion. We need (t:byntree) as argument 
   for Fixpoint definition to be accepted by coq 
*)

Fixpoint byntree_ind_ (t:byntree) : forall (P:byntree -> Prop),
    P bempty                                ->
    (forall (b:yesno), P (bleaf b))         ->
    (forall (b:yesno) (t1 t2:byntree),
        P t1 -> P t2 -> P (bnode b t1 t2))  -> P t :=
        fun (P:byntree -> Prop)                                 =>
            fun (H0:P bempty)                                   =>
                fun (H1:forall (b:yesno), P (bleaf b))          =>
                    fun (H2: forall (b:yesno) (t1 t2:byntree),
                        P t1 -> P t2 -> P (bnode b t1 t2))      =>
                            match t with 
                            | bempty         => H0
                            | bleaf b        => H1 b
                            | bnode b t1 t2  => 
                               (H2 b t1 t2 
                                    (byntree_ind_ t1 P H0 H1 H2) 
                                    (byntree_ind_ t2 P H0 H1 H2))
                            end.


(* This is a manual proof of our manual induction principle *)

Definition byntree_ind' : byntree_ind'_principle :=
    fun P H0 H1 H2 t => byntree_ind_ t P H0 H1 H2.


Inductive ExSet : Type := 
| con1 : bool -> ExSet
| con2 : nat  -> ExSet -> ExSet
.
(*
Check ExSet_ind.
*)




