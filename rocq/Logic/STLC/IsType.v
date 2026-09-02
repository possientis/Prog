Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Context.

Declare Scope STLC_IsType_scope.

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

Lemma IsTypeTS : forall (b v:Type) (G:@Context b v) (t:b) (Ty:T b),
    G :> Ty -> (G ; t ::: *) :> Ty.
Proof.
    intros b v G t Ty H1. revert t.
    induction H1 as [G t H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros t'. apply TVar, FindTS. assumption.
    - intros t'. apply TFun.
        + apply IH1.
        + apply IH2.
Qed.

Lemma IsTypeFS : forall (b v:Type) (G:Context) (x:v) (Ty Ty':T b),
    G :> Ty -> (G ; x ::: Ty') :> Ty.
Proof.
    intros b v G x Ty Ty' H1. revert x Ty'.
    induction H1 as [G t H2|G Ty Ty' H2 IH1 H3 IH2].
    - intros x' Sy. apply TVar, FindTS. assumption.
    - intros x' Sy. apply TFun.
        + apply IH1.
        + apply IH2.
Qed.

Lemma IsTypeRev : forall (b v:Type) (G:@Context b v) (Ty Ty':T b),
    G :> (Ty :-> Ty') -> G :> Ty /\ G :> Ty'.
Proof.
    intros b v G Ty Ty' H1. remember (Ty :-> Ty') as Sy eqn:E.
    revert Ty Ty' E. destruct H1 as [G t|G Ty Ty' H2 H3]; intros Sy Sy' H4.
    - inversion H4.
    - inversion H4. subst. split; assumption.
Qed.

Lemma IsTypeRevL : forall (b v:Type) (G:@Context b v) (Ty Ty':T b),
    G :> (Ty :-> Ty') -> G :> Ty.
Proof.
    intros b v G Ty Ty' H1. 
    apply IsTypeRev in H1. destruct H1 as [H1 H2]. assumption.
Qed.

Lemma IsTypeRevR : forall (b v:Type) (G:@Context b v) (Ty Ty':T b),
    G :> (Ty :-> Ty') -> G :> Ty'.
Proof.
    intros b v G Ty Ty' H1. 
    apply IsTypeRev in H1. destruct H1 as [H1 H2]. assumption.
Qed.

(* A variable binding in context is irrelevant for well-formed-ness             *)
Lemma IsTypeIrrelevant : forall (b v:Type) (G:Context) (x:v) (Ty Ty':T b),
    (G ; x ::: Ty) :> Ty' -> G :> Ty'.
Proof.
    intros b v G x Ty Ty' H1. remember (G ; x ::: Ty) as G' eqn:E.
    revert G x Ty E. induction H1 as [G t|G Ty Ty' H2 IH1 H3 IH2];
    intros G' x Sy H4; subst.
    - apply TVar. apply findTRev with x Sy. assumption.
    - apply TFun.
        + apply IH1 with x Sy. reflexivity.
        + apply IH2 with x Sy. reflexivity.
Qed.
