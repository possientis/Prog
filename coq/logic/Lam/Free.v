Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Remove.
Require Import Injective.

Require Import Lam.T.
Require Import Lam.Variable.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a lambda abstraction, we need to be able to remove a variable    *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint free (v:Type) (e:Eq v) (t:T v) : list v :=
    match t with
    | Var x         => [x]
    | App t1 t2     => free v e t1 ++ free v e t2
    | Lam x t1      => remove e x (free v e t1)
    end.

Arguments free {v} _ _.

(* The free variables of the term (fmap f t) are a subset of the images by f    *)
(* of the free variables of the term t.                                         *)
Lemma free_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    incl (free e' (fmap f t)) (map f (free e t)).
Proof.
    intros v w e e' f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove e' (f x) (map f (free e t1))). 
        + apply remove_mon, IH1.
        + apply incl_tran with (map f (remove e x (free e t1))).
            { apply remove_map. }
            { apply incl_refl. }
Qed.

(*
Lemma free_injective : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v),
    injective_on (var t) f -> free e' (fmap f t) = map f (free e t).
Proof.
    intros v w e e' f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; intros H.
    - reflexivity.
    - rewrite map_app, IH1, IH2.
        + reflexivity.
        + apply injective_on_appr with (var t1). assumption.
        + apply injective_on_appl with (var t2). assumption.
    - rewrite IH1.

Show.
*)


