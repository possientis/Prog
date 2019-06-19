Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Remove.
Require Import Fol.P.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a forall quantification, we need to be able to remove a variable *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint free (v:Type) (e:Eq v) (p:P v) : list v :=
    match p with
    | Bot           => [ ]
    | Elem x y      => [x;y]
    | Imp p1 p2     => free v e p1 ++ free v e p2
    | All x p1      => remove e x (free v e p1)
    end.

Arguments free {v} _ _.


(* The free variables of the proposition (fmap f p) are a subset of the images  *)
(* by f of the free variables of the proposition p.                             *)
Lemma free_fmap : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (p:P v),
    incl (free e' (fmap f p)) (map f (free e p)).
Proof.
    intros v w e e' f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove e' (f x) (map f (free e p1))). 
        + apply remove_mon, IH1.
        + apply incl_tran with (map f (remove e x (free e p1))).
            { apply remove_map. }
            { apply incl_refl. }
Qed.

