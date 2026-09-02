Require Import list.

Inductive prod (a b:Type) : Type :=
    | pair : a -> b -> prod a b
    .

Arguments pair {a} {b} _ _. (* type arguments are inferred *)


Notation "( x , y )" := (pair x y).

(*
(* syntactic sugar only when parsing types *)
Notation "a * b" := (prod a b) : type_scope.
*)

(*
Check (34,67).
Check (true,0).
*)

Definition fst (a b:Type) (p : prod a b ) : a :=
    match p with
    | (x,y)     => x
    end.

Arguments fst {a} {b} _.

Example test_fst : fst (0,true) = 0.
Proof. reflexivity. Qed.

Definition snd (a b:Type) (p: prod a b) : b :=
    match p with
    | (x,y)     => y
    end.

Arguments snd {a} {b} _.

Example test_snd : snd (0,true) = true.
Proof. reflexivity. Qed.


(* 'zip' is called 'combined' coq *)
Fixpoint combine (a b: Type) (l : list a) (k: list b) : list (prod a b) := 
    match l with
    | []        => []
    | x::xs     =>
        match k with
        | []        => []
        | y::ys     => (x,y)::combine a b xs ys
        end
    end.

Arguments combine {a} {b} _ _.


Example test_combine : combine [1,2,3] [true,false] = [(1,true),(2,false)].
Proof. reflexivity. Qed.


(* 'unzip' is called 'split' in coq and is right inverse of zip *)

Fixpoint split (a b:Type) (l : list (prod a b)) : prod (list a) (list b) :=
    match l with
    | []            => ([],[])
    | (u,v)::xs     => (u :: fst (split a b xs), v :: snd (split a b xs))
    end.

Arguments split {a} {b} _.

Example test_split : split [(1,false),(2,true)] = ([1,2],[false,true]).
Proof. reflexivity. Qed.



Theorem combine_split : forall (a b:Type) (l: list (prod a b)),
    combine (fst (split l)) (snd (split l)) = l. 

Proof.
    induction l as [|x xs H].
    - reflexivity.
    - destruct x as [u v]. simpl. rewrite H. reflexivity.
Qed.

Theorem combine_split' : 
    forall (a b:Type) (l:list (prod a b)) (l1: list a) (l2:list b),
    split l = (l1,l2) -> combine l1 l2 = l.
Proof.
    intros a b l l1 l2 H.
    assert (l1 = fst (split l)) as H1. { rewrite H. reflexivity. }
    assert (l2 = snd (split l)) as H2. { rewrite H. reflexivity. }
    rewrite H1, H2. apply combine_split.
Qed.

Theorem split_combine : forall (a:Type) (l k:list a),
    length l = length k -> split (combine l k) = (l,k).
Proof.
    induction l as [|x xs H].
    - destruct k. 
        + intros. reflexivity.
        + simpl. intros H0. inversion H0.
    - induction k as [|y ys H'].
        + simpl. intros H0. inversion H0.
        + simpl. intros H0. rewrite (H ys). simpl. reflexivity.
            inversion H0. reflexivity.
Qed.



