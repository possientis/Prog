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
