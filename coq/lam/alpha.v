Require Import List.
Import ListNotations.

Require Import eq.
Require Import term.
Require Import free.
Require Import vsubst.



(* This inductive predicate defines alpha-equivalence           *)
(* There are four ways of establishing alpha-equivalence        *)
(* 1. Given a variable x:v, we always have x ~ x.               *)
(* 2. t1 ~ t1' and t2 ~ t2' implies t1 t2 ~ t1' t2'             *)
(* 3. t1 ~ t1' implies Lam x t1 ~ Lam x t1'                     *)
(* 4. The final and most interesting way relies on swap         *)
(* In order to establish the equivalence Lam x t1 ~ Lam y t1'   *)
(* in the case when x <> y, we need to ensure that y is not     *)
(* a free variable of t1, and furthermore that t1' ~ t1[x:y]    *)
(* i.e. that t1' is equivalent to t1 after x and y have been    *)
(* exchanged for one another. Note that we cannot do away with  *)
(* the third constructor (by removing condition x <> y in 4.)   *)
(* Lam x (Var x) ~ Lam x (Var x) cannot be proven simply by     *)
(* taking x = y in a variant of 4. because of the requirement   *)
(* that y be not a free variable of t1.                         *)

Inductive alpha (v:Type) (p:Eq v) : P v -> P v -> Prop :=
| AVar  : forall (x:v), alpha v p (Var x) (Var x)
| AApp  : forall (t1 t1' t2 t2':P v), 
    alpha v p t1 t1' -> alpha v p t2 t2' -> alpha v p (App t1 t2) (App t1' t2')
| ALam1 :forall (x:v) (t1 t1':P v), 
    alpha v p t1 t1' -> alpha v p (Lam x t1) (Lam x t1') 
| ALam2 : forall (x y:v) (t1 t1':P v),
    x <> y -> ~In y (Fr p t1) -> alpha v p t1' (swap p x y t1) ->
    alpha v p (Lam x t1) (Lam y t1')
.

Arguments alpha {v} _ _ _.

(*
Lemma alpha_free : forall (v:Type) (p:Eq v) (t t':P v),
    alpha p t t' -> Fr p t = Fr p t'.
Proof.
    intros v p t t' H.
    induction H.
    - reflexivity.
    - simpl.
        assert (Fr p t1 = Fr p t1') as E1. { assumption. }
        assert (Fr p t2 = Fr p t2') as E2. { assumption. }
        rewrite E1, E2. reflexivity.
    - simpl.
        assert (Fr p t1 = Fr p t1') as E1. { assumption. }
        rewrite E1. reflexivity.
    - simpl.
Show.
*)

(*
Lemma alpha_refl: forall (v:Type) (p:Eq v) (t:P v), alpha p t t.
Proof.
    intros v p t.
    induction t.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
Qed.
*)

(*
Lemma alpha_sym: forall (v:Type) (p:Eq v) (t t':P v), 
    alpha p t t' -> alpha p t' t.
Proof.
    intros v p t t' H. 
    induction H.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
    - constructor.
        + intros E. apply H. symmetry. assumption.
        +

Show.
*)


