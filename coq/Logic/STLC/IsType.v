Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Context.

Inductive IsType (b v:Type) : @Context b v -> T b -> Prop :=
| TVar : forall (G:Context) (Ty:b), 
    G :> Ty -> 
    IsType b v G (Base Ty)  
| TFun : forall (G:Context) (Ty Ty':T b),
    IsType b v G Ty     -> 
    IsType b v G Ty'    -> 
    IsType b v G (Ty :-> Ty') 
.

Arguments IsType {b} {v}.
Arguments TVar   {b} {v}.
Arguments TFun   {b} {v}.

Notation "G :- Ty" := (IsType G Ty)
    (at level 1, no associativity) : STLC_IsType_scope.

Open Scope STLC_IsType_scope.
