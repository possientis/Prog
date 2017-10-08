Require Import nat.
Require Import bool.

Module NATLIST.

Inductive natprod : Type :=
    | pair : nat -> nat -> natprod
    .
(*
Check pair 3 5.
*)

Definition fst (p:natprod) : nat :=
    match p with
        | pair x y  => x
    end.

Definition snd (p:natprod) : nat :=
    match p with
        | pair x y => y
    end.
(*
Compute fst (pair 3 5).
Compute snd (pair 3 5).
*)

Notation "( x , y )" := (pair x y).
(*
Compute fst (3,5).
Compute snd (3,5).
*)

Definition fst' (p:natprod) : nat :=
    match p with
        | (x,y) => x
    end.

Definition snd' (p:natprod) : nat :=
    match p with
        | (x,y) => y
    end.
(*
Compute fst' (3,5).
Compute snd' (3,5).
*)

Definition swap_pair (p:natprod) : natprod :=
    match p with
        | (x,y) => (y,x)
    end.
(*
Compute swap_pair (3,5).
*)

Theorem surjective_pairing' : forall n m:nat, 
    (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing : forall p:natprod,
    p = (fst p, snd p).
Proof.
    destruct p as [n m]. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall p:natprod,
    (snd p, fst p) = swap_pair p.
Proof.
    destruct p as [n m]. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall p:natprod,
    fst (swap_pair p) = snd p.
Proof.
    destruct p as [n m]. reflexivity.
Qed.


Inductive natlist : Type :=
    | nil : natlist
    | cons: nat -> natlist -> natlist
    .

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..). (* syntax file has bug *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1,2,3].

Example test1 : mylist1 = mylist.
Proof. reflexivity. Qed.


Example test2 : mylist2 = mylist.
Proof. reflexivity. Qed.


Example test3 : mylist3 = mylist.
Proof. reflexivity. Qed.

(*
Check []. Check [1].
*)

Fixpoint repeat (n count:nat) : natlist :=
    match count with
        | 0     => nil
        | S p   => n :: repeat n p
    end.

(*
Compute repeat 3 10.
*)

Fixpoint length (l:natlist) : nat :=
    match l with
        | nil       => 0
        | _::k      => S (length k)
    end.

(*
Compute length [1,2,3,4,5].
*)

Fixpoint app (l1 l2:natlist) : natlist :=
    match l1 with
        | nil       => l2
        | x::xs     => x :: app xs l2
    end.
(*
Compute app [1,2,3] [4,5,6].
*)

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1 : [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.


Definition hd (default:nat)(l:natlist) : nat :=
    match l with
        | nil       => default
        | x::ls     => x
    end.

Definition tl (l:natlist) : natlist :=
    match l with
        | nil       => nil
        | x::ls     => ls
    end.

Example test_hd1 : hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.


Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl1 : tl [] = [].
Proof. reflexivity. Qed.

Example test_tl2 : tl [1,2,3] = [2,3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
        | nil       => nil
        | x::ls     => 
            match x with
                | 0     => nonzeros ls
                | S p   => (S p) :: nonzeros ls
            end
    end.

Example test_nonzeros : nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddnumbers (l:natlist) : natlist :=
    match l with
        | nil       => nil
        | x::ls     => 
           if oddb x
              then x::oddnumbers ls
              else oddnumbers ls
    end.
                 
Example test_oddnumbers : oddnumbers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2:natlist) : natlist :=
    match l1, l2 with
        | nil, nil           => nil
        | nil, y::k2         => l2
        | x::k1, nil         => l1
        | (x::k1), (y::k2)   => x::y::alternate k1 k2
    end.

Example test_alternate1 : alternate [] [] = [].
Proof. reflexivity. Qed.


Example test_alternate2 : alternate [1,2,3] [] = [1,2,3].
Proof. reflexivity. Qed.


Example test_alternate3 : alternate [] [1,2,3] = [1,2,3].
Proof. reflexivity. Qed.


Example test_alternate4 : alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. reflexivity. Qed.


Example test_alternate5 : alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed.

Example test_alternate6 : alternate [1,2,3] [4] = [1,4,2,3].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
        |  nil      =>  0
        |  x::xs    =>  if eqb v x
            then S (count v xs)
            else count v xs
    end.

Example test_count1 : count 1 [1,2,3,1,4,1] = 3. 
Proof. reflexivity. Qed.

Example test_count2 : count 1 [] = 0.
Proof. reflexivity. Qed.

Example test_count3 : count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := fun a b => a ++ b.

Example test_sum1 : count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1 : count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.


Example test_add2 : count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := negb ( eqb (count v s) 0).

Example test_member1 : member 1 [1,4,1] = true.
Proof. reflexivity. Qed.


Example test_member2 : member 2 [1,4,1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
        | nil     => nil
        | x::xs   => if eqb v x
            then xs
            else x :: remove_one v xs
    end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4: count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.


Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
        | nil       => nil
        | x::xs     => if eqb v x 
            then remove_all v xs
            else x :: remove_all v xs
    end.

Example test_remove_all1 : count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2 : count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3 : count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4 : count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
        | nil       => true
        | x::xs     => member x s2 && subset xs (remove_one x s2)
    end.

Example test_subset1 : subset [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.

Example test_subset2 : subset [1,2,2] [2,1,4,1] = false.
Proof. reflexivity. Qed.

Theorem bag_theorem : forall (v:nat) (s:bag), 
    count v (add v s) = S (count v s). 
Proof.
    (* induction hypothesis is not needed, destruct works just as well *)
    destruct s as [|x xs].
    - simpl. rewrite eqb_n_n. reflexivity.
    - simpl. rewrite eqb_n_n. reflexivity.
Qed.



