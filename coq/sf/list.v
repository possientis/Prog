Require Import bool.
Require Import nat.
Require Import Setoid.

Inductive list (a:Type) : Type :=
    | nil  : list a
    | cons : a -> list a -> list a
    .

Arguments nil {a}.
Arguments cons {a} _ _.

Fixpoint repeat (a:Type) (x:a) (count:nat):list a :=
    match count with
    | 0     => nil
    | S n   => cons x (repeat a x n)
    end.

Arguments repeat {a} _ _.


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

Fixpoint length (a:Type) (l:list a) : nat :=
    match l with
    | []        => 0
    | (_::xs)   => S (length a xs)
    end.
        
Arguments length {a} _.


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


Lemma app_cons : forall (a:Type) (l k:list a) (x:a),
    (x :: l) ++ k = x :: (l ++ k).
Proof. reflexivity. Qed.


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
        



