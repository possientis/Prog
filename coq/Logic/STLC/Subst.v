Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.STLC.Syntax.

Fixpoint subst_(b v:Type)(e:Eq v)(f:v -> Exp b v)(xs:list v)(t:Exp b v):Exp b v:=
    match t with
    | Ann t' Ty => Ann (subst_ b v e f xs t') Ty
    | Var x     =>
        match in_dec eqDec x xs with
        | left _    => Var x    (* x is deemed bound    -> Var x                *)
        | right _   => f x      (* x is deemed free     -> f x                  *)
        end
    | App t1 t2 => App (subst_ b v e f xs t1) (subst_ b v e f xs t2)
    | Lam x t1  => Lam x (subst_ b v e f (x :: xs) t1)  (* x now bound          *)
    end.
Arguments subst_ {b} {v} {e}.

Definition subst(b v:Type)(e:Eq v)(f:v -> Exp b v)(t:Exp b v):Exp b v:=
    subst_ f [] t.

Arguments subst {b} {v} {e}.

Lemma substAnn : forall (b v:Type)(e:Eq v)(f:v -> Exp b v)(t:Exp b v)(Ty:T b),
    subst f (Ann t Ty) = Ann (subst f t) Ty.
Proof. intros b v e f t Ty. reflexivity. Qed.

Lemma substVar : forall (b v:Type)(e:Eq v)(f:v -> Exp b v)(x:v),
    subst f (Var x) = f x.
Proof. intros b v e f x. reflexivity. Qed.

Lemma substApp : forall (b v:Type)(e:Eq v)(f:v -> Exp b v)(t1 t2:Exp b v),
    subst f (App t1 t2) = App (subst f t1) (subst f t2).
Proof. intros b v e f t1 t2. reflexivity. Qed.

