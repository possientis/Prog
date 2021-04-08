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

Lemma notIsTypeInO : forall (b v:Type) (Ty:T b), ~ @IsType b v O Ty.
Proof.
    intros b v Ty H1. remember O as G eqn:E. revert E.
    induction H1 as [G Ty H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros H3. subst. inversion H2.
    - assumption.
Qed.

(*
Lemma IsTypeRev : forall (b v:Type) (G:@Context b v) (Ty:b) (Ty':T b),
    (G ; Ty ::: * ) :- Ty' -> Ty' = (Base Ty) \/ G :- Ty'.
Proof.
    intros b v G Ty Ty' H1. remember (G ; Ty ::: * ) as G' eqn:E. 
    revert G Ty E. induction H1 as [G Ty H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros G' Sy H4. subst. apply findTyRev' in H2. destruct H2 as [H2|H2].
        + subst. left. reflexivity.
        + right. constructor. assumption.
    - intros G' Sy H4. right. constructor.
      specialize IH1 with G' Sy. specialize IH2 with G' Sy.
      destruct (IH1 H4) as [H5|H5]; destruct (IH2 H4) as [H6|H6].
        + 
Show.
*)
