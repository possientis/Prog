(* This module has no equivalent in Fol                                         *)

Require Import List.
Import ListNotations.

Require Import Eq.

Require Import Lam.T.

Fixpoint subst_ (v:Type) (e:Eq v) (f:v -> T v) (xs:list v) (t:T v) : T v :=
    match t with
    | Var x     =>
        match in_dec e x xs with
        | left _    => Var x    (* x is deemed bound    -> Var x                *)
        | right _   => f x      (* x is deemed free     -> f x                  *)
        end
    | App t1 t2 => App (subst_ v e f xs t1) (subst_ v e f xs t2)
    | Lam x t1  => Lam x (subst_ v e f (x :: xs) t1)        (* x now bound      *)
    end.

Arguments subst_ {v}.

Definition subst (v:Type) (e:Eq v) (f:v -> T v) (t:T v) : T v :=
    subst_ e f [] t.

Arguments subst {v}.

Lemma substVar : forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (x:v),
    t = Var x -> subst e f t = f x.
Proof. intros v e f t x H. rewrite H. reflexivity. Qed.

Lemma substApp : forall (v:Type) (e:Eq v) (f:v -> T v) (t1 t2 t:T v),
    t = App t1 t2 -> subst e f t = App (subst e f t1) (subst e f t2).
Proof. intros v e f t1 t2 t H. rewrite H. unfold subst. simpl. reflexivity. Qed.  


