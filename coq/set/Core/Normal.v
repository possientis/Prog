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

Lemma normalEquiv : forall (x:set), x == normal x.
Proof.
    induction x as [|x IH1 xs IH2].
    - apply equalRefl.
    - simpl. destruct (elem_dec x xs) as [H|H]; simpl.
        +  apply equalTrans with xs.
            { apply consIn. assumption. }
            { apply IH2. }
        + apply equalTrans with (insert x xs).
            { apply equalSym. apply insertCons. }
            { apply insertCompatLR.
                { apply IH1. }
                { apply IH2. }}
Qed.
 

Lemma normalEqualEquiv : forall (x y:set), normal x = normal y -> x == y.
Proof.
    intros x y H. apply equalTrans with (normal y).
    - apply equalTrans with (normal x).
        + apply normalEquiv.
        + rewrite H. apply equalRefl.
    - apply equalSym. apply normalEquiv.
Qed.


