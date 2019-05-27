Require Import List.

Require Import Fol.P.

(* We do not have sets: the variables of a formula are a list, not a set.       *)

Fixpoint var (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => nil
    | Elem x y  => cons x (cons y nil)
    | Imp p1 p2 => var v p1 ++ var v p2
    | All x p1  => cons x (var v p1)
    end.

Arguments var {v} _.


Lemma var_fmap : forall (v w:Type) (f:v -> w) (p:P v),
    var (fmap f p) = map f (var p).
Proof.
    intros v w f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

