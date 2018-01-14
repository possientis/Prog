Require Import bool.
Require Import induction.
Require Import Setoid.

Inductive list (a:Type) : Type :=
    | nil  : list a
    | cons : a -> list a -> list a
    .


(*
Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).
*)


Fixpoint repeat {a:Type} (x:a) (count:nat) : list a :=
    match count with
    | 0     => nil a
    | S n   => cons a x (repeat x n)
    end.


Example repeat_test1 : repeat 3 0 = nil nat.
Proof. reflexivity. Qed.


Example repeat_test2 : repeat 3 1 = cons nat 3 (nil nat).
Proof. reflexivity. Qed.


Example repeat_test3 : repeat 3 2 = cons nat 3 (cons nat 3 (nil nat)).
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
    | 0     => nil a
    | S n   => cons a x (repeat' a x n)
    end.


Fixpoint repeat'' a x count : list a :=
    match count with
    | 0     => nil a
    | S n   => cons a x (repeat'' a x n)
    end.

Fixpoint repeat''' a x count : list a :=
    match count with
    | 0     => nil _
    | S n   => cons _ x (repeat''' _ x n)
    end.

(*
Check repeat.
Check repeat'.
Check repeat''.
Check repeat'''.
*)


Definition list123  := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {a}.
Definition list123'' := cons _ 1 (cons _ 2 (cons _ 3 nil)).

Arguments cons {a} _ _.
Definition list123''' := cons 1 (cons 2 (cons 3 nil)).


Example test_list123_1 : list123 = list123'.
Proof. reflexivity. Qed. 

Example test_list123_2 : list123 = list123''.
Proof. reflexivity. Qed. 

Example test_list123_3 : list123 = list123'''.
Proof. reflexivity. Qed. 

Notation "x :: xs" := (cons x xs) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..). (* syntax file has bug *)


Fixpoint app (a:Type) (k l: list a) : list a :=
    match k with
    | []        => l
    | x::xs     => x :: (app a xs l)
    end.  
     
Arguments app {a} _ _. (* type argument declared as implicit *)

Notation "l ++ k" := (app l k) (at level 60, right associativity). 


(* need a type annotation, as no other way for it to be inferred *)
Example test_app1 : forall a:Type, [] ++ [] = ([] : list a).
Proof. reflexivity. Qed.

Example test_app2 : forall (a:Type) (l:list a), [] ++ l = l.
Proof. reflexivity. Qed.

Example test_app3 : [1,2,3] ++ [4,5,6] = [1,2,3,4,5,6].
Proof. reflexivity. Qed.

Theorem  app_nil_r : forall (a:Type) (l:list a), l ++ [] = l.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - simpl. rewrite H. reflexivity.
Qed.

(* not computationally efficient *)
Fixpoint rev (a:Type) (l:list a) : list a :=
    match l with
    |   []          => []
    |   x :: xs     => (rev a xs) ++ [x]
    end.

Arguments rev {a} _.

Example test_rev1 : forall a:Type, rev [] = ([]:list a). 
Proof. reflexivity. Qed.

Example test_rev2 : rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.

Fixpoint length (a:Type) (l:list a) : nat :=
    match l with
    | []        => 0
    | (_::xs)   => S (length a xs)
    end.
        
Arguments length {a} _.

Example test_length1 : forall a:Type, length ([]:list a) = 0.
Proof. reflexivity. Qed.

Example test_length2 : length [1,2,3] = 3.
Proof. reflexivity. Qed.

Definition my_nil1 := ([]:list nat).
Definition my_nil2 : list nat := nil.
Definition my_nil3 := @nil.

Theorem app_assoc : forall (a:Type) (l m n: list a),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - simpl. intros m n. rewrite H. reflexivity.
Qed. 


Theorem app_length : forall (a:Type) (l k: list a),
    length (l ++ k) = length l + length k.
Proof.
    induction l as [| x xs H].
    - reflexivity.
    - intro k. simpl. rewrite H. reflexivity.
Qed.

Theorem rev_app_distr : forall (a:Type) (l k: list a),
    rev (l ++ k) = rev k ++ rev l.
Proof.
    induction l as [| x xs H].
    - intro k. simpl. rewrite app_nil_r. reflexivity.
    - intro k. simpl. rewrite H. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall (a:Type) (l: list a),
    rev (rev l) = l.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - simpl. rewrite rev_app_distr. simpl. rewrite H. reflexivity.
Qed.

(* we are not using app_length, exercise *)
Theorem app_length_cons : forall (a:Type) (l k:list a) (x:a) (n:nat),
    length (l ++ (x :: k)) = n -> S (length (l ++ k)) = n.
Proof.
    intros a l. induction l as [|y ys H].
    - intros k x n. simpl. intros H. exact H.
    - intros k x n. simpl. destruct n.
        + intros H'. inversion H'.
        + intros H'. inversion H' as [H1]. clear H'.
            rewrite H1. apply H in H1. rewrite H1. reflexivity.
Qed.

(* we are not using app_length, exercise *)
Theorem app_length_twice : forall (a:Type) (n:nat) (l:list a),
    length l = n -> length (l ++ l) = n + n.
Proof.
    intros a n l. generalize n. clear n. induction l as [|x xs H].
    - destruct n.
        + intros. reflexivity.
        + intros H. inversion H.
    - destruct n.
        + intros H'. inversion H'.
        + intros H'. inversion H' as [H1]. clear H'.
            simpl. rewrite H1. rewrite (plus_comm n (S n)).
            simpl. apply H in H1. 
            assert ( S (length (xs ++ xs)) = length (xs ++ x :: xs)) as H'.
                { apply app_length_cons with (x:=x). reflexivity. }
            rewrite <- H'. rewrite H1. reflexivity.
Qed.


Fixpoint rev_append (a:Type) (l acc:list a) : list a :=
    match l with 
    | []        => acc
    | x :: xs   => rev_append a xs (x :: acc) 
    end.

Arguments rev_append {a} _ _.

(* tr for tail-recursive *)
Definition tr_rev (a:Type) (l: list a) : list a := rev_append l []. 


Arguments tr_rev {a} _.

Lemma app_cons : forall (a:Type) (l k:list a) (x:a),
    (x :: l) ++ k = x :: (l ++ k).
Proof. reflexivity. Qed.

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

Fixpoint eqb_list (a:Type)(eqb: a -> a -> bool) (l k:list a) : bool :=
    match l with 
    | []        =>
        match k with
        | []        => true
        | _ :: _    => false
        end
    | x :: xs   =>
        match k with
        | []        => false
        | y :: ys   => eqb x y && eqb_list a eqb xs ys
        end 
    end.

Arguments eqb_list {a} _ _ _.

Lemma eqb_list_true_iff : forall (a:Type) (eqb: a -> a -> bool),
    (forall x y, eqb x y = true <-> x = y) ->
    (forall l k, eqb_list eqb l k = true <-> l = k).
Proof.
    intros a eqb H. split.
    - generalize k. clear k. induction l as [|x xs IH].
        + intros [|y ys].
            { intros. reflexivity. }
            { intros H'. inversion H'. }
        + intros [|y ys].
            { intros H'. inversion H'. }
            { intros H'. simpl in H'. rewrite andb_true_iff in H'. 
                destruct H' as [H1 H2]. destruct (H x y) as [H' H''].
                apply H' in H1. rewrite H1. 
                assert (xs = ys) as E. { apply IH. exact H2. }
                rewrite E. reflexivity. }
    - generalize k. clear k. induction l as [|x xs IH].
        + intros [|y ys].
            { intros. reflexivity. }
            { intros H'. inversion H'. }
        + intros [|y ys].
            { intros H'. inversion H'. }
            { intros H'. inversion H'. simpl. apply andb_true_iff. split.
                { apply H. reflexivity. }
                { rewrite <- H2. apply IH. reflexivity. } } 
Qed.


Lemma length_0_iff_nil : forall (a:Type) (l:list a),
    length l = 0 <-> l = nil.
Proof.
    intros a l. split.
    - destruct l as [|x xs].
        + intros. reflexivity.
        + intros H. inversion H.
    - intros H. rewrite H. reflexivity.
Qed.

Lemma l_not_cons_l : forall (a:Type) (l:list a) (x:a),
    ~ (l = x :: l).
Proof.
    intros a l. induction l as [|x xs IH].
    - intros x H. inversion H.
    - intros y H. inversion H. apply (IH y). exact H2.
Qed.

Lemma l_not_l_app : forall (a:Type) (l:list a) (x:a),
    ~ (l = l ++ [x]).
Proof.
    intros a l x H. remember (rev l) as l' eqn:H'.
    assert (l' = x :: l') as H0.
    { rewrite H'. rewrite H at 1. rewrite rev_app_distr. reflexivity. }
    revert H0. apply l_not_cons_l.
Qed.

Lemma list_3_cases : forall (a:Type) (l:list a), 
    l = []                              \/
    (exists x, l = [x])                 \/
    (exists x y k, l = x :: k ++ [y])   .
Proof.
    intros a l. induction l as [|x xs [IH|[[y IH]|[x' [y [k IH]]]]]].
    - left. reflexivity.
    - right. left. exists x. rewrite IH. reflexivity.
    - right. right. exists x, y, []. rewrite IH. reflexivity.
    - right. right. exists x, y, (x' :: k). rewrite IH. 
        rewrite app_cons. reflexivity.
Qed.

Lemma app_cons' : forall (a:Type) (l k:list a) (x:a),
    l ++ x :: k = (l ++ [x]) ++ k.
Proof.
    intros a l. induction l as [|x xs IH].
    - intros k x. reflexivity.
    - intros k y. rewrite app_cons, app_cons, app_cons.
        rewrite <- (IH k y). reflexivity.
Qed.

Lemma app_injective_l : forall (a:Type) (l k m:list a),
    k ++ l = m ++ l -> k = m.
Proof.
    intros a l. induction l as [|x xs IH].
    - intros k m H. rewrite app_nil_r in H. rewrite app_nil_r in H. exact H.
    - intros k m H.
      rewrite (app_cons' a k xs x) in H. 
      rewrite (app_cons' a m xs x) in H. 
      apply IH in H.
      assert (rev (k ++ [x])  = rev (m ++ [x])) as H'.
      { rewrite H. reflexivity. }
      rewrite rev_app_distr in H'.
      rewrite rev_app_distr in H'.
      simpl in H'. inversion H' as [H0].
      rewrite <- (rev_involutive a k).
      rewrite <- (rev_involutive a m).
      rewrite H0. reflexivity.
Qed.

Lemma app_injective_r : forall (a:Type) (l k m:list a),
    l ++ k = l ++ m -> k = m.
Proof.
    intros a l. induction l as [|x xs IH].
    - intros k m H. exact H.
    - intros k m H. rewrite app_cons in H. rewrite app_cons in H.
        inversion H as [H']. apply IH. exact H'.
Qed.


Lemma rev_list_3_cases : forall (a:Type) (l:list a), l = rev l -> 
    l = []                                          \/ 
    (exists x, l = [x])                             \/
    (exists x k, l = x :: k ++ [x] /\ k = rev k)    .
Proof.
    intros a l H. 
    assert (l = [] \/ (exists x,l = [x]) \/ 
        (exists x y k, l = x :: k ++ [y])) as [H'|[[x H']|[x [y [k H']]]]]. 
        { apply list_3_cases. }
    - left. exact H'.
    - right. left. exists x. exact H'.
    - right. right. exists x, k.
        rewrite H' in H at 2. simpl in H. rewrite rev_app_distr in H.
        simpl in H. rewrite H' in H. inversion H as [H0]. split.
        + rewrite H', H0. reflexivity.
        + apply app_injective_l with (l:=[y]). exact H1. 
Qed.
        










