Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Remove.
Require Import Include.

Require Import Fol.P.
Require Import Fol.Free.
Require Import Fol.Variable.

Fixpoint bnd (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => []
    | Elem x y  => []
    | Imp p1 p2 => bnd v p1 ++ bnd v p2
    | All x p1  => x :: bnd v p1
    end.


Arguments bnd {v} _.


Lemma bnd_var : forall (v:Type) (p:P v), incl (bnd p) (var p).
Proof.
    intros v.
    induction p as [|x y|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - intros z H. inversion H.
    - apply incl_app2; assumption.
    - apply incl_cons2. assumption.
Qed.


