Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Context.

Inductive IsType (b v:Type) : @Context b v -> T b -> Prop :=
| TVar : forall (G:Context) (t:b), 
    G :> t -> 
    IsType b v G (Base t)  
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

Lemma notIsTypeInO : forall (b v:Type) (Ty:T b), ~ @IsType b v O Ty.
Proof.
    intros b v Ty H1. remember O as G eqn:E. revert E.
    induction H1 as [G Ty H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros H3. subst. inversion H2.
    - assumption.
Qed.
