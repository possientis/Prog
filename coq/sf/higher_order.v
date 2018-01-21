Require Import list.
Require Import bool.
Require Import nat.
Require Import In.
Require Import list.
Require Import filter.

Definition doit3times (a:Type) (f:a->a) (x:a) : a := f (f (f x)).

Arguments doit3times {a} _ _.

(*
Check @doit3times.
*)

Example test_filter1 : filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition of_length_1 (a:Type) (l:list a) : bool := eqb (length l) 1.

Arguments of_length_1 {a} _.

Example test_filter2 : filter of_length_1 [[1,2],[3],[4],[5,6,7],[],[8]] =
    [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition countoddnumbers' (l:list nat) : nat := length (filter oddb l).

Example test_countoddnumbers'1 : countoddnumbers'[1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.


Example test_countoddnumbers'2 : countoddnumbers' [0,2,4] = 0.
Proof. reflexivity. Qed.

Example test_countoddnumbers'3 : countoddnumbers' [] = 0.
Proof. reflexivity. Qed.

Example test_anonymous_fun' : doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2' : filter (fun l => eqb (length l) 1)
    [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.


Definition filter_even_gt7 (l:list nat) : list nat :=
    filter (fun n => evenb n && ltb 7 n) l. 

Example test_filter_even_gt7_1 :
    filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2:
    filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.
    
Definition partition (a:Type)(test: a -> bool)(l:list a):prod (list a)(list a) :=
    let l1 := filter test l in
        let l2 := filter (fun x => negb (test x)) l in (l1,l2).
    
Arguments partition {a} _ _.

Example test_partition1 : partition oddb [1,2,3,4,5] = ([1,3,5],[2,4]).
Proof. reflexivity. Qed.

Example test_partition2 : partition (fun x => false) [5,9,0] = ([],[5,9,0]).
Proof. reflexivity. Qed.

Theorem filter_exercise : forall (a:Type) (test: a -> bool) (x:a) (l k:list a),
    filter test l = x :: k -> test x = true.
Proof.
    induction l as [|y ys H].
    - intros k H. inversion H.
    - intros k H0. destruct (test y) eqn:H'.
        + simpl in H0. rewrite H' in H0. inversion H0 as [H1].
            rewrite H1 in H'. exact H'.
        + simpl in H0. rewrite H' in H0. apply (H k). exact H0. 
Qed.


Fixpoint forallb (a:Type) (test: a -> bool) (l:list a) : bool :=
    match l with
    | []        =>  true
    | x :: xs   =>  if test x then forallb a test xs else false 
    end.

Arguments forallb {a} _ _.

Example test_forallb1 : forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity. Qed.

Example test_forallb2 : forallb negb [false,false] = true.
Proof. reflexivity. Qed.

Example test_forallb3 : forallb evenb [0,2,4,5] = false.
Proof. reflexivity. Qed.

Example test_forallb4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existb (a:Type) (test: a -> bool) (l:list a) : bool :=
    match l with
    | []        =>  false
    | x :: xs   =>  if test x then true else existb a test xs
    end.

Arguments existb {a} _ _.

Example test_existb1 : existb (eqb 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.


Example test_existb2 : existb (andb true) [false,true,false] = true.
Proof. reflexivity. Qed.

Example test_existb3 : existb oddb [1,0,0,0,3] = true.
Proof. reflexivity. Qed.

Example test_existb4 : existb evenb [] = false.
Proof. reflexivity. Qed.

Definition existb' (a:Type) (test: a -> bool) (l:list a) : bool :=
    negb (forallb (fun x => negb (test x)) l).

Arguments existb' {a} _ _.

Theorem existb_existb' : forall (a:Type) (test: a -> bool) (l:list a),
    existb test l = existb' test l.
Proof.
    intros a test l. induction l as [|x xs H].  
    - reflexivity.
    - destruct (test x) eqn:H'.  
        + unfold existb, existb', forallb, negb. rewrite H'. reflexivity.
        + unfold existb. rewrite H'. fold (existb test xs).
            unfold existb'. unfold forallb. rewrite H'. simpl.
            fold (forallb (fun x => negb (test x)) xs).
            fold (existb' test xs). exact H.
Qed.


Fixpoint All (a:Type) (test: a -> Prop) (l: list a) : Prop :=
    match l with 
    | []        => True
    | x :: xs   => test x /\ All a test xs
    end.

Arguments All {a} _ _.

Theorem forallb_true_iff : forall (a:Type) (test: a -> bool) (l:list a),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
    intros a test l. split.
    - induction l as [|x xs H].
        + intros. apply I.
        + intros H'. split.
            { destruct (test x) eqn: Tx.
                { reflexivity. }
                { simpl in H'. rewrite Tx in H'. inversion H'. } }
            { apply H. destruct (test x) eqn: Tx. 
                { simpl in H'. rewrite Tx in H'. exact H'. }
                { simpl in H'. rewrite Tx in H'. inversion H'. } }
    - induction l as [|x xs H].
        + intros. reflexivity.
        + intros [H1 H2]. simpl. rewrite H1. apply H. exact H2.
Qed.






