Require Import Logic.Class.Eq.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.

Require Import Logic.Fol.Syntax.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Context.

(* Just so the predicate Eval can have two arguments instead of three.          *)
Inductive Interpretation : Type :=
| mkInterp : forall (p:Formula) (A:Prop), Interpretation
.

Notation "p >> P" := (mkInterp p P)
    (at level 1, no associativity) : Context_scope.

Open Scope Context_scope.

Inductive Eval : Context -> Interpretation -> Prop :=
| EvalBot  : forall (G:Context), Eval G Bot >> False
| EvalElem : forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x -> G :> m~>y -> Eval G (Elem n m) >> (x :: y)
| EvalImp  : forall (G:Context) (p1 p2:Formula) (A1 A2:Prop), 
    Eval G p1 >> A1 -> Eval G p2 >> A2 -> Eval G (Imp p1 p2) >> (A1 -> A2)
|EvalAll   : forall (G:Context) (n:nat) (p1:Formula) (A1:set -> Prop),
    (forall (x:set), Eval (G ; n~>x) p1 >> (A1 x)) ->
    Eval G (All n p1) >> (forall (x:set), A1 x)
.

Notation "G :- I" := (Eval G I)
    (at level 60, no associativity).

Open Scope Context_scope.

(* Just restating constructor EvalBot with custom notations.                    *)
Lemma evalBot : forall (G:Context), G :- Bot >> False.
Proof.
    intros G. constructor.
Qed.

(* Just restating constructor EvalElem with custom notations.                   *)
Lemma evalElem : forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x -> G :> m~>y -> G :- (Elem n m) >> (x :: y).
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

(* Just restating constructor EvalImp with custom notations.                    *)
Lemma evalImp : forall (G:Context) (p1 p2:Formula) (A1 A2:Prop),
    G :- p1 >> A1 -> G :- p2 >> A2 -> G :- (Imp p1 p2) >> (A1 -> A2).
Proof.
    intros G p1 p2 A1 A2 H1 H2. constructor; assumption.
Qed.

(* Just restating constructor EvalAll with custom notations.                    *)
Lemma evalAll : forall (G:Context) (n:nat) (p1:Formula) (A1:set -> Prop),
    (forall (x:set), G ; n~>x :- p1 >> (A1 x)) -> 
        G :- (All n p1) >> (forall (x:set), A1 x).
Proof.
    intros G n p1 A1 H1. constructor. assumption.
Qed.

Lemma evalMonotone : forall (G H:Context) (p:Formula) (A:Prop),
    G <= H -> G :- p >> A -> H :- p >> A.
Proof.
    intros G H p A H1 H2. revert H H1. induction H2 as 
        [G|G n m x y H1 H2|G p1 p2 A1 A2 H1 IH1 H2 IH2|G n p1 A1 H1 IH1]; 
    intros H H3.
    - apply evalBot.
    - apply evalElem; apply H3; assumption.
    - apply evalImp.
        + apply IH1. assumption.
        + apply IH2. assumption.
    - apply evalAll. intros x. apply IH1. apply ctxInclExtend. assumption.
Qed.

Lemma evalWeaken : forall (G:Context) (p:Formula) (A:Prop),
    O :- p >> A -> G :- p >> A.
Proof.
    intros G p A. apply evalMonotone, ctxInclO.
Qed.

(*
Lemma evalDrop : forall (G:Context) (p:Formula) (n:nat) (x y:set) (A : Prop),
    G ; n~>y ; n~>x :- p >> A -> G ; n~>x :- p >> A.
Proof.
    intros G p n x y A H1. remember (G ; n~>y ; n~>x) as G1 eqn:E1.
    revert G n x y E1. induction H1 as
        [G'|G' n m x y H1 H2|G' p1 p2 A1 A2 H1 IH1 H2 IH2|G' n p1 A1 H1 IH1];
    intros G n' x' y' H3.
    - apply evalBot.
    - subst. apply evalElem.
        +  destruct (eqDec n' n) as [H4|H4].
            { subst. apply bindEqualRev in H1. apply FindE with x';
              try assumption. apply FindZ. }
            { apply bindDiff; try assumption. 
              apply bindDiff in H1; try assumption. 
              apply bindDiff in H1; assumption. }
        + destruct (eqDec n' m) as [H4|H4].
            { subst. apply bindEqualRev in H2. apply FindE with x';
              try assumption. apply FindZ. }
            { apply bindDiff; try assumption.
              apply bindDiff in H2; try assumption. 
              apply bindDiff in H2; assumption. }
    - subst. apply evalImp.
        + apply IH1 with y'. reflexivity.
        + apply IH2 with y'. reflexivity.
    - subst. apply evalAll. intros x.

Show.
*)
