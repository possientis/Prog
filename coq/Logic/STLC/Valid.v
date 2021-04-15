Require Import Logic.Class.Eq.

Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

(* This predicate expresses the fact that the context G is a valid context.     *)
(* Valid0 : The empty context is valid.                                         *)
(* ValidTy: Adding a type variable declaration to a valid context is valid.     *)
(* ValidVar: Adding a variable declaration with a well-formed type expression   *)
(* to a valid context yields a valid context.                                   *)
Inductive Valid (b v:Type) : @Context b v -> Prop :=
| ValidO : Valid b v O
| ValidT : forall (G:Context) (t:b),
    Valid b v G -> Valid b v (G ; t ::: *)
| ValidV : forall (G:Context) (x:v) (Ty:T b),
    Valid b v G -> G :> Ty -> Valid b v (G ; x ::: Ty) 
.

Arguments Valid  {b} {v}.
Arguments ValidO {b} {v}.
Arguments ValidT {b} {v}.
Arguments ValidV {b} {v}.

(*
(* The type expression of a binding of a valid context is always well-formed.   *)
Lemma ValidIsType : forall (b v:Type) (eq:Eq v) (G:@Context b v) (x:v) (Ty:T b),
    Valid G -> G :>> x ::: Ty -> G :> Ty.
Proof.
    intros b v eq G x Ty H1. revert x Ty.
    induction H1 as [ |G t H1 IH|G x Ty H1 IH H2].
    - intros x' Ty' H3. inversion H3.
    - intros x' Ty' H3. remember (G ; t ::: * ) as G' eqn:E.
      remember (x' ::: Ty') as k eqn:F. revert G t H1 IH x' Ty' E F.
      destruct H3 as [G x Ty|G k t H4|G x y Ty Ty' H4 H5];
      intros G' t' H6 H7 y' Sy H8 H9. 
        + inversion H8.
        + inversion H8. subst. apply IsTypeS. apply H7 with y'. assumption.
        + inversion H8.
    -
Show.
*)
