(* TODO: check imports are really needed                                        *)

Require Import Core.Set.
Require Import Core.Leq.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Cons.
Require Import Core.Equal.
Require Import Core.Order.
Require Import Core.Empty.
Require Import Core.Insert.
Require Import Core.ElemIncl.
Require Import Core.Decidability.
Require Import Core.Extensionality.

Fixpoint normal (x:set) : set :=
    match x with
    | Nil           => Nil
    | (Cons x xs)   =>
        match (elem_dec x xs) with
        | left _    => normal xs                        (*  we have x :: xs     *)
        | right _   => insert (normal x) (normal xs)    (*  otherwise           *)
        end
    end.

Lemma normalSame : forall (x:set), normal x == x.
Proof.
    induction x as [|x IH1 xs IH2].
    - apply equalRefl.
    - simpl. destruct (elem_dec x xs) as [H|H]; simpl.
        +  apply equalTrans with xs.
            { apply IH2. }
            { apply equalSym. apply consIn. assumption. }
        + apply equalTrans with (insert x xs).
            { apply insertCompatLR.
                { apply IH1. }
                { apply IH2. }}
            { apply insertCons. }
Qed.
 

Lemma normalEqual : forall (x y:set), normal x = normal y -> x == y.
Proof.
    intros x y H. apply equalTrans with (normal y).
    - apply equalTrans with (normal x).
        + apply equalSym. apply normalSame.
        + rewrite H. apply equalRefl.
    - apply normalSame.
Qed.

(*
Lemma equalNormal_n : forall (n:nat) (x y:set),
    order x + order y <= n -> x == y -> normal x = normal y.
Proof.
    induction n as [|n IH].
    - admit.
    - intros x y H1 H2. destruct x as [|x xs].
        + admit.
        + simpl. destruct (elem_dec x xs) as [H3|H3]; simpl.
            { admit. }
            { destruct y as [|y ys].
                { admit. }
                { simpl. destruct (elem_dec y ys) as [H4|H4]; simpl.
                    { admit. }
                    {
Show.
*)


