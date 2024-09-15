Require Import Bool.

Require Import Logic.Prop.Syntax.

(* Predicate defining a valuation                                               *)
Definition Valuation (v:Type) (f:P v -> bool) : Prop
  := f (Bot) = false
  /\ forall (p q:P v) , f (p :-> q) = negb (f p) || f q.

Arguments Valuation {v}.

Lemma valBot : forall (v:Type) (f:P v -> bool),
  Valuation f -> f Bot = false.
Proof.
  intros v f [HBot HImp]. exact HBot.
Qed.

Arguments valBot {v} {f}.

Lemma valImp : forall (v:Type) (f:P v -> bool),
  Valuation f -> forall (p q:P v), f (p :-> q) = negb (f p) || f q.
Proof.
  intros v f [HBot HImp]. exact HImp.
Qed.

Arguments valImp {v} {f}.

Lemma valNot : forall (v:Type) (f:P v -> bool),
  Valuation f -> forall (p:P v), f (¬p) = negb (f p).
Proof.
  intros v f HVal p. rewrite (valImp HVal), (valBot HVal).
  destruct (f p); reflexivity.
Qed.

Arguments valNot {v} {f}.

Lemma valAnd : forall (v:Type) (f:P v -> bool),
  Valuation f -> forall (p q:P v), f (and p q) = f p && f q.
Proof.
  intros v f HVal p q. unfold and.
  rewrite (valNot HVal), (valImp HVal), (valNot HVal).
  destruct (f p), (f q); reflexivity.
Qed.

Arguments valAnd {v} {f}.

Lemma valOr : forall (v:Type) (f:P v -> bool),
  Valuation f -> forall (p q:P v), f (or p q) = f p || f q.
Proof.
  intros v f HVal p q. unfold or.
  rewrite (valImp HVal), (valNot HVal).
  destruct (f p), (f q); reflexivity.
Qed.

Arguments valOr {v} {f}.

(* Two valuations which coincide on variables are equal *)
Lemma coincideValuation : forall (v:Type) (f g:P v -> bool),
  Valuation f               ->
  Valuation g               ->
  (forall (x:v), f 'x = g 'x) ->
  forall (p:P v), f p = g p.
Proof.
  intros v f g Hf Hg HVar.
  induction p as [|x|p IHp q IHq].
  - rewrite (valBot Hf), (valBot Hg). reflexivity.
  - apply HVar.
  - rewrite (valImp Hf), (valImp Hg), IHp, IHq. reflexivity.
Qed.

(* Valuation associated with a truth assignment *)
Fixpoint eval (v:Type) (f:v -> bool) (p:P v ) : bool
  := match p with
      | Bot => false
      | Var x => f x
      | Imp p' q' => negb (eval v f p') || eval v f q'
     end.
Arguments eval {v}.

(* For every truth assignment f: v -> bool, eval f is indeed a valuation *)
Lemma evalValuation : forall (v:Type) (f:v -> bool), Valuation (eval f).
Proof.
  intros v f. split.
    - reflexivity.
    - intros p q. reflexivity.
Qed.

(* Given a truth assignment f:v -> bool, eval f is the only valuation which     *)
(* coincide with f on variables.                                                *)
Lemma evalUnique : forall (v:Type) (f:v -> bool) (g :P v -> bool),
  Valuation g ->
  (forall (x:v), f x = g 'x) ->
  forall (p:P v), eval f p = g p.
Proof.
  intros v f g Hg HVar. apply coincideValuation.
    - apply evalValuation.
    - apply Hg.
    - apply HVar.
Qed.

(* Restrict a map f:P v -> bool to its associated truth assignment              *)
Definition restrict (v:Type) (f:P v -> bool) (x:v) : bool := f 'x.

Arguments restrict {v}.

(* A valuation is just the eval of its associated truth assignment              *)
Lemma valIsEval : forall (v:Type) (f:P v -> bool),
  Valuation f -> forall (p:P v), f p = eval (restrict f) p.
Proof.
  intros v f Hf p. apply coincideValuation.
    - apply Hf.
    - apply evalValuation.
    - intros x. reflexivity.
Qed.
