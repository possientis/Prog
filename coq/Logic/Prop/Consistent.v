Require Import List.

Require Import Logic.List.In.

Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Proof.
Require Import Logic.Prop.Semantics.
Require Import Logic.Prop.Entails.
Require Import Logic.Prop.Sound.

(* There is no proof of bottom from the empty context *)
Lemma consistent : forall (v:Type), ~ exists (e:nil :- @bot v), True.
Proof.
  (* Let v be a Type and e be a proof of bottom from the empty context *)
  intros v [e _].

  (* We need to arrive at a contradiction *)
  assert False as A. 2: apply A.

  (* We have nil ::- bot from the soundness property *)
  apply soundness in e.

  (* Consider an arbitrary truth assignment *)
  remember (fun (x:v) => true) as f eqn:F.

  (* Our contradiction is eval f bot = true *)
  assert (eval f bot = true) as C. 2: inversion C.

  (* So we need to show that eval f bot = true *)
  assert (eval f bot = true) as A. 2: apply A.

  (* Using nil ::- bot *)
  apply e.

  (* We need to show that all q's in the empty context are true *)
  assert (forall (q:P v), q :: nil -> eval f q = true) as A. 2: apply A.

  (* which is vacuously the case *)
  intros q H. inversion H.
Qed.
