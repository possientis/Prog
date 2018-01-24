Require Import list.

(*
Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).
*)

Example repeat_test1 : repeat 3 0 = [].
Proof. reflexivity. Qed.


Example repeat_test2 : repeat 3 1 = cons 3 [].
Proof. reflexivity. Qed.


Example repeat_test3 : repeat 3 2 = cons 3 (cons 3 []).
Proof. reflexivity. Qed.

Module MUMBLEGRUMBLE.

Inductive mumble : Type :=
    | a : mumble
    | b : mumble -> nat -> mumble
    | c : mumble
    .

Inductive grumble (X:Type) : Type :=
    | d : mumble -> grumble X
    | e : X      -> grumble X
    .
(*
Check d mumble (b a 5). (* grumble mumble *)
Check d bool   (b a 5). (* grumble bool *)
Check e bool true.      (* grumble bool *)
Check e mumble (b c 0). (* grumble mumble *)
Check c.                (* mumble *)
*)

End MUMBLEGRUMBLE.

Fixpoint repeat' (a:Type) (x:a) (count:nat) : list a :=
    match count with
    | 0     =>  []
    | S n   => cons x (repeat' a x n)
    end.


Fixpoint repeat'' a x count : list a :=
    match count with
    | 0     => []
    | S n   => cons x (repeat'' a x n)
    end.

Definition list123  := cons 1 (cons 2 (cons 3 [])).
Definition list123' := @cons _ 1 (@cons _ 2 (@cons _ 3 (@nil _))).


Arguments nil {a}.
Definition list123'' := @cons _ 1 (@cons _ 2 (@cons _ 3 nil)).

Arguments cons {a} _ _.
Definition list123''' := cons 1 (cons 2 (cons 3 nil)).


Example test_list123_1 : list123 = list123'.
Proof. reflexivity. Qed. 

Example test_list123_2 : list123 = list123''.
Proof. reflexivity. Qed. 

Example test_list123_3 : list123 = list123'''.
Proof. reflexivity. Qed. 


(* need a type annotation, as no other way for it to be inferred *)
Example test_app1 : forall a:Type, [] ++ [] = ([] : list a).
Proof. reflexivity. Qed.

Example test_app2 : forall (a:Type) (l:list a), [] ++ l = l.
Proof. reflexivity. Qed.

Example test_app3 : [1,2,3] ++ [4,5,6] = [1,2,3,4,5,6].
Proof. reflexivity. Qed.

Example test_rev1 : forall a:Type, rev [] = ([]:list a). 
Proof. reflexivity. Qed.

Example test_rev2 : rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.

Example test_length1 : forall a:Type, length ([]:list a) = 0.
Proof. reflexivity. Qed.

Example test_length2 : length [1,2,3] = 3.
Proof. reflexivity. Qed.

Definition my_nil1 := ([]:list nat).
Definition my_nil2 : list nat := nil.
Definition my_nil3 := @nil.


Fixpoint rev_append (a:Type) (l acc:list a) : list a :=
    match l with 
    | []        => acc
    | x :: xs   => rev_append a xs (x :: acc) 
    end.

Arguments rev_append {a} _ _.

(* tr for tail-recursive *)
Definition tr_rev (a:Type) (l: list a) : list a := rev_append l []. 


Arguments tr_rev {a} _.

Lemma rev_append_assoc : forall (a:Type) (l k m: list a),
    rev_append l k ++ m = rev_append l (k ++ m).
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - intros k m. simpl. rewrite H. rewrite app_cons. reflexivity.
Qed.

Theorem tr_rev_cons : forall (a:Type) (l:list a) (x:a),
    tr_rev (x :: l) = tr_rev l ++ [x].
Proof.
    induction l as [|y xs H].
    - intros x. reflexivity.
    - intros x. unfold tr_rev. simpl. unfold tr_rev in H. 
        rewrite rev_append_assoc. simpl. reflexivity.
Qed.


Theorem tr_rev_app_distr : forall (a:Type) (l k: list a),
    tr_rev (l ++ k) = tr_rev k ++ tr_rev l.
Proof.
    induction l as [|x xs H].
    - intros k. unfold tr_rev. simpl. symmetry. apply app_nil_r.
    - intros k. rewrite app_cons. rewrite tr_rev_cons, tr_rev_cons.
        rewrite H. rewrite app_assoc. reflexivity.
Qed.


Lemma tr_rev_correct : forall (a:Type) (l:list a),
    tr_rev l = rev l.
Proof.
    intros a l. induction l as [|x xs H].
    - reflexivity.
    - simpl. rewrite tr_rev_cons. rewrite H. reflexivity.
Qed.


