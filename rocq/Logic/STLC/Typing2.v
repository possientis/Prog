(* This module only serves to demonstrate that defining the typing relation     *)
(* with stronger requirements in terms of context validity and well-formedness  *)
(* of type expressions is unnecessary and yields an equivalent notion.          *)
Require Import Logic.Class.Eq.

Require Import Logic.STLC.Valid.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Typing.
Require Import Logic.STLC.Context.

Inductive Judgement2 (b v:Type) (eq:Eq v): Context -> Typing -> Prop :=
| JAnn2 : forall (G:Context) (e:Exp b v) (Ty:T b),
    Valid G                                     ->  (* superfluous              *)
    G :> Ty                                     ->  (* superfluous              *)
    Judgement2 b v eq G (e >: Ty)               ->
    Judgement2 b v eq G ((e :: Ty) >: Ty)    
| JVar2 : forall (G:Context) (x:v) (Ty:T b),
    Valid G                                     -> 
    G :> Ty                                     ->  (* superfluous              *)
    G :>> x ::: Ty                              -> 
    Judgement2 b v eq G (`x >: Ty)            
| JApp2 : forall (G:Context) (e1 e2:Exp b v) (Ty Ty':T b),
    Valid G                                     ->  (* superfluous              *)
    G :> Ty                                     ->  (* superfluous              *)
    G :> Ty'                                    ->  (* superfluous              *)
    Judgement2 b v eq G (e1 >: Ty :-> Ty')      ->  
    Judgement2 b v eq G (e2 >: Ty)              -> 
    Judgement2 b v eq G (e1 $ e2 >: Ty')        
| JLam2 : forall (G:Context) (x:v) (e:Exp b v) (Ty Ty':T b),
    Valid G                                     ->  
    G :> Ty                                     ->  
    Judgement2 b v eq (G;x ::: Ty) (e >: Ty')   ->  
    Judgement2 b v eq G ((\x ~> e) >: Ty :-> Ty')
.

Arguments Judgement2 {b} {v} {eq}.
Arguments JAnn2      {b} {v} {eq}.
Arguments JVar2      {b} {v} {eq}.
Arguments JApp2      {b} {v} {eq}.
Arguments JLam2      {b} {v} {eq}.

(* Building a proof of Judgment2 requires more evidence that for building a     *)
(* proof of Judgment. Hence expecting the following implication to hold.        *)
Lemma Judgement2Judgement : 
    forall (b v:Type) (eq:Eq v) (G:Context) (e:Exp b v) (Ty:T b),
        Judgement2 G (e >: Ty) -> G :- e >: Ty.
Proof.
    intros b v eq G e Ty H1. remember (e >: Ty) as k eqn:E. revert e Ty E.
    induction H1 as 
        [ G e Ty H2 H3 H4 IH
        | G x Ty H2 H3 H4  
        | G e1 e2 Ty Ty' H2 H3 H4 H5 IH1 H6 IH2
        | G x e Ty Ty' H2 H3 H4 IH 
        ]; intros e' Sy H7; inversion H7; subst; clear H7. 
    - apply JAnn. apply IH with e Sy. reflexivity.
    - apply JVar; assumption.
    - apply JApp with Ty.
        + apply IH1 with e1 (Ty :-> Sy). reflexivity.
        + apply IH2 with e2 Ty. reflexivity.
    - apply JLam; try assumption. apply IH with e Ty'. reflexivity.
Qed.


(* However, we know that a Judgement cannot hold unless the context is valid    *)
(* and the type expression is well-formed. So the following should hold.        *)
 Lemma JudgementJudgement2 : 
    forall (b v:Type) (eq:Eq v) (G:Context) (e:Exp b v) (Ty:T b),
        G :- e >: Ty -> Judgement2 G (e >: Ty).
Proof.
    intros b v eq G e Ty H1. remember (e >: Ty) as k eqn:E. revert e Ty E.
    induction H1 as
        [ G e Ty H2 IH
        | G x Ty H2 H3 
        | G e1 e2 Ty Ty' H2 IH1 H3 IH2
        | G x e Ty Ty' H2 H3 H4 IH 
        ]; intros e' Sy H7; inversion H7; subst; clear H7. 
    - apply JAnn2.
        + apply TypedIsValid with eq e Sy. assumption.
        + apply TypedIsType with eq e. assumption.
        + apply IH with e Sy. reflexivity.
    - apply JVar2; try assumption. apply ValidIsType with eq x; assumption.
    - apply JApp2 with Ty.
        + apply TypedIsValid with eq e2 Ty. assumption.
        + apply TypedIsType with eq e2. assumption.
        + apply IsTypeRevR with Ty. apply TypedIsType with eq e1. assumption.
        + apply IH1 with e1 (Ty :-> Sy). reflexivity.
        + apply IH2 with e2 Ty. reflexivity.
    - apply JLam2; try assumption. apply IH with e Ty'. reflexivity.
Qed.

(* This vindicates our streamlined definition of the Judgement predicate.       *)
Theorem JudgementJudgement2Same:
    forall (b v:Type) (eq:Eq v) (G:Context) (e:Exp b v) (Ty:T b),
        G :- e >: Ty <-> Judgement2 G (e >: Ty).
Proof.
    intros b v eq G e Ty. split; intros H1.
    - apply JudgementJudgement2. assumption.
    - apply Judgement2Judgement. assumption.
Qed.
