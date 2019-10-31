Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Order.
Require Import Core.Equal.
Require Import Core.Decidability. 
Require Import Core.Extensionality.

(* The set 'x' is ::-minimal in the set 'xs'                                    *)
Definition minimal (x xs:set) : Prop :=
    x :: xs /\ ~ exists (y:set), y :: xs /\ y :: x.


(* No set can belong to itself                                                  *)
Lemma elemSelf : forall (x y:set), x <== y -> ~ y :: x.
Proof.
    induction x as [|x IH1 xs IH2].
    - admit.
    - intros y H1 H2. apply consElem in H2.

Show.



(*
(* The foundation axiom is satisfied in 'set'                                   *) 
Theorem foundation : forall (x:set), ~(x == Nil) -> 
    exists (y:set), minimal y x.
Proof.
    induction x as [|x _ xs IH].
    - admit.
    - intros _. destruct (equal_dec xs Nil) as [H|H].
        + exists x. unfold minimal. split.
            { apply consElem. left. apply equal_refl. }
            { intros H'.

Show.
*)
