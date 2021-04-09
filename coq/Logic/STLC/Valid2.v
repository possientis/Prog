Require Import Logic.STLC.Valid.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

Inductive Valid2 (b v:Type) : @Context b v -> Prop :=
| Valid2O   : Valid2 b v O
| Valid2Ty  : forall (G:Context) (t:b),
    Valid2 b v G -> Valid2 b v (G ; t ::: *)
| Valid2Var : forall (G:Context) (x:v) (Ty:T b),
    Valid2 b v G -> IsType2 b v G Ty -> Valid2 b v (G ; x ::: Ty) 
with IsType2 (b v:Type) : @Context b v -> T b -> Prop :=
| TVar2 : forall (G:Context) (t:b),
    Valid2 b v G ->
    G :> t      ->
    IsType2 b v G (Base t)
| TFun2 : forall (G:Context) (Ty Ty':T b),
    Valid2 b v G        ->
    IsType2 b v G Ty    ->
    IsType2 b v G Ty'   ->
    IsType2 b v G (Ty :-> Ty')
.

Arguments Valid2    {b} {v}.
Arguments Valid2O   {b} {v}.
Arguments Valid2Ty  {b} {v}.
Arguments Valid2Var {b} {v}.
Arguments IsType2   {b} {v}.
Arguments TVar2     {b} {v}.
Arguments TFun2     {b} {v}.

(* The defining requirements for IsType2 appear to be stronger than those of    *)
(* IsType, so we expect the implication IsType2 G Ty -> IsType G Ty to hold.    *)
(* Note that we do not expect the reverse implication to be true.               *)
Lemma IsType2IsType : forall (b v:Type) (G:@Context b v) (Ty:T b),
    IsType2 G Ty -> G :- Ty.
Proof.
   intros b v G Ty H1. induction H1 as [G Ty H2 H3|G Ty Ty' H2 H3 IH1 H4 IH2]. 
   - constructor. assumption.
   - constructor; assumption.
Qed.

(* The defining requirements for Valid2 are based on a stronger IsType2, so we  *)
(* expect the implication Valid2 G -> Valid G to hold.                          *)
Lemma Valid2Valid : forall (b v:Type) (G:@Context b v),
    Valid2 G -> Valid G.
Proof.
    intros b v G H1. induction H1 as [ |G Ty H2 IH|G x Ty H2 IH H3]. 
    - constructor.
    - constructor. assumption.
    - constructor; try assumption. apply IsType2IsType. assumption.
Qed.

Lemma ValidValid2IsType2 : forall (b v:Type) (G:@Context b v),
    Valid G -> Valid2 G /\ (forall (Ty:T b), G :- Ty -> IsType2 G Ty).
Proof.
    intros b v G H1. induction H1 as [ |G t H2 IH|G x Ty H2 IH H3].
    - split; try constructor. intros Ty H2. 
      apply notIsTypeInO in H2. contradiction.
    - destruct IH as [IH1 IH2]. split.
        + constructor. assumption.
        + intros Ty H3.
Show.
