Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.STLC.Syntax.

Fixpoint subst_(b v:Type)(eq:Eq v)(f:v -> Exp b v)(xs:list v)(e:Exp b v):Exp b v:=
    match e with
    | Ann e' Ty => Ann (subst_ b v eq f xs e') Ty
    | Var x     =>
        match in_dec eqDec x xs with
        | left _    => Var x    (* x is deemed bound    -> Var x                *)
        | right _   => f x      (* x is deemed free     -> f x                  *)
        end
    | App t1 t2 => App (subst_ b v eq f xs t1) (subst_ b v eq f xs t2)
    | Lam x t1  => Lam x (subst_ b v eq f (x :: xs) t1)  (* x now bound         *)
    end.
Arguments subst_ {b} {v} {eq}.

Definition subst(b v:Type)(eq:Eq v)(f:v -> Exp b v)(e:Exp b v):Exp b v:=
    subst_ f [] e.

Arguments subst {b} {v} {eq}.

Lemma substAnn : forall (b v:Type)(eq:Eq v)(f:v -> Exp b v)(e:Exp b v)(Ty:T b),
    subst f (Ann e Ty) = Ann (subst f e) Ty.
Proof. intros b v eq f e Ty. reflexivity. Qed.

Lemma substVar : forall (b v:Type)(eq:Eq v)(f:v -> Exp b v)(x:v),
    subst f (Var x) = f x.
Proof. intros b v eq f x. reflexivity. Qed.

Lemma substApp : forall (b v:Type)(eq:Eq v)(f:v -> Exp b v)(e1 e2:Exp b v),
    subst f (App e1 e2) = App (subst f e1) (subst f e2).
Proof. intros b v eq f e1 e2. reflexivity. Qed.

