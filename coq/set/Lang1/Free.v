Require Import List.
Require Import Peano_dec.

Require Import Lang1.Syntax.


(* Free variables of a formula.                                                 *)
Fixpoint Fr (p:Formula) : list nat :=
    match p with
    | Bot       => nil
    | Elem n m  => cons n (cons m nil)
    | Imp p q   => Fr p ++ Fr q
    | All n p   => remove (eq_nat_dec) n (Fr p)
    end.  

(*
Lemma free_map : forall (f:nat -> nat) (p:Formula),
    incl (Fr (fmap f p)) (map f (Fr p)).
Proof.
    intros f. induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - apply incl_refl.
    - apply incl_refl.
    - rewrite map_app. apply incl_app.
        + apply incl_appl, IH1.
        + apply incl_appr, IH2.
    - apply incl_tran with (remove eq_nat_dec (f x) (map f (Fr p1))). 

Show.
*)
