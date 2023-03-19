Require Import Logic.Class.Eq.

Require Import Logic.STLC.Valid.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

Declare Scope STLC_Typing_scope.

(* Just so the predicate Judgment can have two arguments instead of three.      *)
Inductive Typing (b v:Type) : Type :=
| mkTyping : forall (e:Exp b v) (Ty:T b), Typing b v
.

Arguments Typing   {b} {v}.
Arguments mkTyping {b} {v}.

Notation "e >: Ty" :=(mkTyping e Ty)
    (at level 25, no associativity)      : STLC_Typing_scope.

Open Scope STLC_Typing_scope.

(* Predicate expressing a typing judgement.                                     *)
Inductive Judgement (b v:Type) (eq:Eq v): Context -> Typing -> Prop :=
| JAnn : forall (G:Context) (e:Exp b v) (Ty:T b),
    Judgement b v eq G (e >: Ty)            ->  (* e is of type Ty in context G *) 
    Judgement b v eq G ((e :: Ty) >: Ty)        (* Annotated expr same type     *)
| JVar : forall (G:Context) (x:v) (Ty:T b),
    Valid G                                 ->  (* G is a valid context         *)
    G :>> x ::: Ty                          ->  (* variable x declared type Ty  *) 
    Judgement b v eq G (`x >: Ty)               (* variable expr same type      *) 
| JApp : forall (G:Context) (e1 e2:Exp b v) (Ty Ty':T b),
    Judgement b v eq G (e1 >: Ty :-> Ty')   ->  (* e1 of type Ty :-> Ty'        *)
    Judgement b v eq G (e2 >: Ty)           ->  (* e2 of type Ty                *)
    Judgement b v eq G (e1 $ e2 >: Ty')         (* e1 e2 of type Ty'            *)
| JLam : forall (G:Context) (x:v) (e:Exp b v) (Ty Ty':T b),
    Valid G                                 ->  (* G is a valid context         *)
    G :> Ty                                 ->  (* Ty well-formed expression    *)
    Judgement b v eq (G;x ::: Ty) (e >: Ty')->  (* e is of type Ty' with x:::Ty *)
    Judgement b v eq G ((\x ~> e) >: Ty :-> Ty')(* \x -> e is of type Ty :-> Ty'*)
.

Arguments Judgement {b} {v} {eq}.
Arguments JAnn      {b} {v} {eq}.
Arguments JVar      {b} {v} {eq}.
Arguments JApp      {b} {v} {eq}.
Arguments JLam      {b} {v} {eq}.

Notation "G :- T" := (Judgement G T)
    (at level 90, no associativity) : STLC_Typing_scope.

Open Scope STLC_Typing_scope.

(* A typing judgement will never hold, unless the context is valid.             *)
Lemma TypedIsValid : forall (b v:Type)(eq:Eq v)(G:Context)(e:Exp b v)(Ty:T b),
    G :- e >: Ty -> Valid G.
Proof.
    intros b v eq G e Ty H1. remember (e >: Ty) as k eqn:E. revert e Ty E.
    induction H1 as 
        [ G e Ty H3 IH
        | G x Ty H3 H4
        | G e1 e2 Ty Ty' H3 IH1 H4 IH2
        | G x e Ty Ty' H3 H4 H5 IH 
        ]; intros e' Sy H2; inversion H2; subst.
    - apply (IH e Sy). reflexivity.
    - assumption.
    - apply (IH2 e2 Ty). reflexivity.
    - assumption.
Qed.


(* A typing judgement will never hold, unless type expression is well-formed    *)
Lemma TypedIsType : forall (b v:Type)(eq:Eq v)(G:Context)(e:Exp b v)(Ty:T b),
    G :- e >: Ty -> G :> Ty.
Proof.
    intros b v eq G e Ty H1. remember (e >: Ty) as k eqn:E. revert e Ty E.
    induction H1 as 
        [ G e Ty H3 IH
        | G x Ty H3 H4
        | G e1 e2 Ty Ty' H3 IH1 H4 IH2
        | G x e Ty Ty' H3 H4 H5 IH 
        ]; intros e' Sy H2; inversion H2; subst; clear H2.
    - apply (IH e). reflexivity.
    - apply (ValidIsType _ _ _ G x); assumption.
    - apply IsTypeRevR with Ty. apply IH1 with e1. reflexivity.
    - apply TFun; try assumption. apply IsTypeIrrelevant with x Ty.
      apply IH with e. reflexivity. 
Qed.

