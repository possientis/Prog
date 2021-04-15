Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Context.

(* This predicate expresses the fact that a type expression Ty is well-formed   *)
(* in a context G. Note that we do not require G to be a valid context.         *)
(* TVar: a base type is well-formed if the corresponding variable is declared.  *)
(* TFun: a function type is well-formed if both types involved are well-formed. *)
Inductive IsType (b v:Type) : @Context b v -> T b -> Prop :=
| TVar : forall (G:Context) (t:b), 
    G >> t -> 
    IsType b v G 't
| TFun : forall (G:Context) (Ty Ty':T b),
    IsType b v G Ty     -> 
    IsType b v G Ty'    -> 
    IsType b v G (Ty :-> Ty') 
.

Arguments IsType {b} {v}.
Arguments TVar   {b} {v}.
Arguments TFun   {b} {v}.

(* The type expression Ty is well-formed in context G.                          *)
Notation "G :> Ty" := (IsType G Ty)
    (at level 1, no associativity) : STLC_IsType_scope.

Open Scope STLC_IsType_scope.

(* No type expression is well-formed in the empty context.                      *)
Lemma notIsTypeInO : forall (b v:Type) (Ty:T b), ~ @IsType b v O Ty.
Proof.
    intros b v Ty H1. remember O as G eqn:E. revert E.
    induction H1 as [G Ty H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros H3. subst. inversion H2.
    - assumption.
Qed.

Lemma IsTypeS : forall (b v:Type) (G:@Context b v) (t:b) (Ty:T b),
    G :> Ty -> (G ; t ::: *) :> Ty.
Proof.
    intros b v G t Ty H1. revert t.
    induction H1 as [G t H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros t'. apply TVar, FindTS. assumption.
    - intros t'. apply TFun.
        + apply IH1.
        + apply IH2.
Qed.
