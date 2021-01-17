Require Import Logic.Class.Eq.

Require Import Logic.Axiom.LEM.

Require Import Logic.Rel.Prop.

Require Import Logic.Nat.Fresh.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Empty.
Require Import Logic.Set.ElemIncl.
Require Import Logic.Set.Foundation.
Require Import Logic.Set.Extensionality.

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
| EvalAll  : forall (G:Context) (n:nat) (p1:Formula) (A1:set -> Prop),
    (forall (x:set), Eval (G ; n~>x) p1 >> (A1 x)) ->
    Eval G (All n p1) >> (forall (x:set), A1 x)
| EvalEqu  : forall (G:Context) (p:Formula) (A B:Prop), 
    A <-> B -> Eval G p >> A -> Eval G p >> B
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
    G :> n~>x -> 
    G :> m~>y -> 
    G :- (Elem n m) >> (x :: y).
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

(* Just restating constructor EvalImp with custom notations.                    *)
Lemma evalImp : forall (G:Context) (p1 p2:Formula) (A1 A2:Prop),
    G :- p1 >> A1 -> 
    G :- p2 >> A2 -> 
    G :- (Imp p1 p2) >> (A1 -> A2).
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
    G <= H      -> 
    G :- p >> A -> 
    H :- p >> A.
Proof.
    intros G H p A H1 H2. revert H H1. induction H2 as 
        [G
        |G n m x y H1 H2
        |G p1 p2 A1 A2 H1 IH1 H2 IH2
        |G n p1 A1 H1 IH1
        |G p' A' B' H1 H2 IH2
        ]; 
    intros H H3.
    - apply evalBot.
    - apply evalElem; apply H3; assumption.
    - apply evalImp.
        + apply IH1. assumption.
        + apply IH2. assumption.
    - apply evalAll. intros x. apply IH1. apply ctxInclExtend. assumption.
    - apply EvalEqu with A'; try assumption. apply IH2. assumption. 
Qed.

Lemma evalCompat : forall (G G':Context) (p:Formula) (A:Prop),
    ctxEqual G G' -> G :- p >> A -> G' :- p >> A.
Proof.
    intros G G' p A [H1 H2] H3. apply evalMonotone with G; assumption.
Qed.

Lemma evalWeaken : forall (G:Context) (p:Formula) (A:Prop),
    O :- p >> A -> 
    G :- p >> A.
Proof.
    intros G p A. apply evalMonotone, ctxInclO.
Qed.

Lemma evalDrop : forall (G:Context) (p:Formula) (n:nat) (x y:set) (A : Prop),
    G ; n~>y ; n~>x :- p >> A -> 
    G ; n~>x :- p >> A.
Proof.
    intros G p n x y A. apply evalMonotone. intros m z H1.
    destruct (eqDec n m) as [H2|H2].
    - subst. apply bindEqualRev in H1. 
      apply FindE with x; try assumption. constructor.
    - apply bindDiff in H1; try assumption.
      apply bindDiff in H1; try assumption.
      apply bindDiff; assumption.
Qed.

Lemma evalSwap : forall (G:Context) (p:Formula) (n m:nat) (x y:set) (A:Prop),
    n <> m                      ->
    G ; m~>y ; n~>x :- p >> A   ->
    G ; n~>x ; m~>y :- p >> A.
Proof.
    intros G p n m x y A H1. apply evalMonotone. intros k z H2.
    destruct (eqDec n k) as [H3|H3].
    - subst. apply bindEqualRev in H2. apply bindDiff.
        + intros H3. apply H1. symmetry. assumption.
        + apply FindE with x; try assumption. constructor.
    - destruct (eqDec m k) as [H4|H4].
        + subst. apply bindDiff in H2; try assumption.
          apply bindEqualRev in H2. 
          apply FindE with y; try assumption. constructor.
        + apply bindDiff in H2; try assumption.
          apply bindDiff in H2; try assumption.
          apply bindDiff; try assumption.
          apply bindDiff; assumption.
Qed.

Lemma evalNot : forall (G:Context) (p:Formula) (A:Prop),
    G :- p >> A  -> 
    G :- (Not p) >> ~A.
Proof.
    intros G p A H1. unfold Not. constructor; try assumption. constructor.
Qed.

Lemma evalOr : LEM -> forall (G:Context) (p q:Formula) (A B:Prop),
    G :- p >> A                 ->
    G :- q >> B                 -> 
    G :- (Or p q) >> (A \/ B).
Proof.
    intros L G p q A B H1 H2. unfold Or. 
    apply EvalEqu with (~A -> B).
    - apply LEMOr. assumption.
    - constructor; try assumption. apply evalNot. assumption.
Qed.

Lemma evalAnd : LEM -> forall (G:Context) (p q:Formula) (A B:Prop),
    G :- p >> A                 ->
    G :- q >> B                 ->
    G :- (And p q) >> (A /\ B).
Proof.
    intros L G p q A B H1 H2. unfold And, Or. 
    apply EvalEqu with (~(~~A -> ~B)).
    - apply LEMAnd. assumption.
    - apply evalNot, evalImp.
        + apply evalNot, evalNot. assumption.
        + apply evalNot. assumption.
Qed.

Lemma evalExi : LEM -> forall (G:Context) (p:Formula) (n:nat) (A:set -> Prop), 
    (forall (x:set), G ; n~>x :- p >> (A x))  ->
    G :- (Exi n p) >> exists (x:set), A x.
Proof.
    intros L G p n A H1. unfold Exi. 
    apply EvalEqu with (~(forall (x:set), ~A x)).
    - apply LEMExist. assumption.
    - apply evalNot, evalAll. intros x. apply evalNot, H1.
Qed.

Lemma evalIff : LEM -> forall (G:Context) (p q:Formula) (A B:Prop),
    G :- p >> A                 ->
    G :- q >> B                 ->
    G :- (Iff p q) >> (A <-> B).
Proof.
    intros L G p q A B H1 H2. unfold Iff.
    apply evalAnd; try assumption; apply evalImp; assumption.
Qed.

(* Needed for set inclusion notation x <= y                                     *)
Open Scope Set_Incl_scope.


(* LEM is not needed for this one.                                              *)
Lemma evalSub : forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x                   ->
    G :> m~>y                   ->
    G :- (Sub n m) >> (x <= y).
Proof.
    intros G n m x y H1 H2. unfold Sub. 
    apply EvalEqu with (forall (z:set), z :: x -> z :: y).
    - rewrite elemIncl. split; auto.
    - apply evalAll. intros z. apply evalImp; apply evalElem; try (apply FindZ);
      apply bindDiff; try assumption.
          + apply freshNot_n.
          + apply freshNot_m.
Qed.

Lemma evalEqu : LEM -> forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x                   ->
    G :> m~>y                   ->
    G :- (Equ n m) >> (x == y).
Proof.
    intros L G n m x y H1 H2. unfold Equ. apply evalAnd; try assumption;
    apply evalAll; intros z; apply evalIff; try assumption; apply evalElem;
    try (apply FindZ); apply bindDiff; try assumption;
    try (apply freshNot_n); apply freshNot_m.
Qed.

Lemma evalEmpty : forall (G:Context) (n:nat) (x:set),
    G :> n~>x                   ->
    G :- (Empty n) >> (x == Nil).
Proof.
    intros G n x H1. unfold Empty. 
    apply EvalEqu with (forall (z:set), ~z :: x).
    - split.
        + apply emptyUnique.
        + intros H2. rewrite emptyIsNil in H2. rewrite H2. apply emptyCharac.
    - apply evalAll. intros z. apply evalNot, evalElem; try (apply FindZ).
      apply bindDiff; try assumption. apply freshNot_n.
Qed.

Lemma evalMin : LEM -> forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x                   ->
    G :> m~>y                   ->
    G :- (Min n m) >> (minimal x y).
Proof.
    intros L G n m x y H1 H2. unfold Min, minimal.
    apply evalAnd; try assumption.
    - apply evalElem; assumption.
    - apply evalNot, evalExi; try assumption. intros z. 
      apply evalAnd; try assumption; apply evalElem; try (apply FindZ);
      apply bindDiff; try assumption;
      try (apply freshNot_n); apply freshNot_m.
Qed.

Lemma evalDeterministic : forall (G:Context) (p:Formula) (A B:Prop),
    G :- p >> A -> G :- p >> B -> A <-> B.
Proof.
    intros G p A B H1. revert B. remember (p >> A) as b eqn:E.
    revert p A E. induction H1 as 
        [G
        |G n m x y H1 H2
        |G p1 p2 A1 A2 H1 IH1 H2 IH2
        |G n p1 A1 H1 IH1
        |G p' A' B' H1 H2 IH2
        ];
    intros p A H3 B H4; inversion H3; subst; clear H3.
    - remember (Bot >> B) as b eqn:E. revert B E. 
      induction H4 as
        [
        |
        |
        |
        | G p' A B H2 H3 IH
        ];
      intros B' H1; inversion H1; subst; clear H1.
        + split; auto.
        + apply equivTrans with A; try assumption. apply IH. reflexivity.
    - remember ((Elem n m) >> B) as b eqn:E. revert n m x y H1 H2 B E.
      induction H4 as
        [
        |
        |
        |
        | G p' A B H2 H3 IH
        ];
      intros n' m' x' y' H4 H5 B' H6; inversion H6; subst; clear H6.
        + split; apply elemCompatLR.
            { apply (bindDeterministic G n'); assumption. }
            { apply (bindDeterministic G m'); assumption. }
            { apply (bindDeterministic G n'); assumption. }
            { apply (bindDeterministic G m'); assumption. }
        + apply equivTrans with A; try assumption. apply (IH n' m' x' y');
          try assumption. reflexivity. 
    - remember ((Imp p1 p2) >> B) as b eqn:E. 
      revert p1 p2 A1 A2 H1 H2 IH1 IH2 B E.
      induction H4 as
        [
        |
        |
        |
        | G p' A B H2 H3 IH
        ];
      intros p1' p2' A1' A2' H4 H5 H6 H7 B' H9; inversion H9; subst; clear H9.
        + apply implyCompatLR.
            { apply H6 with p1'; try assumption. reflexivity. }
            { apply H7 with p2'; try assumption. reflexivity. }
        + apply equivTrans with A; try assumption.
          apply (IH p1' p2'); try assumption. reflexivity.
    - remember ((All n p1) >> B) as b eqn:E.
      revert n p1 A1 H1 IH1 B E.
      induction H4 as
        [
        |
        |
        |
        | G p' A B H2 H3 IH
        ];
        intros n' p1' A1' H4 H5 B' H6; inversion H6; subst; clear H6.
        + apply allCompat. intros x. apply (H5 x p1'); try reflexivity. apply H.
        + apply equivTrans with A; try assumption.
          apply (IH n' p1'); try assumption. reflexivity.
    - apply equivTrans with A'. 
        + apply equivSym. assumption.
        + apply IH2 with p; try assumption. reflexivity.
Qed.

