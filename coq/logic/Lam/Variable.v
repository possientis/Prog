Require Import List.

Require Import Lam.T.

(* We do not have sets: the variables of a term are a list, not a set.          *)

Fixpoint var (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => cons x nil
    | App t1 t2 => var v t1 ++ var v t2
    | Lam x t1  => cons x  (var v t1)
    end.

Arguments var {v} _.


Lemma var_fmap : forall (v w:Type) (f:v -> w) (t:T v),
    var (fmap f t) = map f (var t).
Proof.
    intros v w f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

