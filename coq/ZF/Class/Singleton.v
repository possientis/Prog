Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

(* The class of all singletons.                                                 *)
Definition Singleton : Class := fun x => exists y, x = :{y}:.

Proposition IsProper : Proper Singleton.
Proof.
  (* Assume Singleton is small. *)
  intros H1. assert (Small Singleton) as A. apply H1. clear A.

  (* We need to arrive at the contradiction *)
  assert (False) as A. 2: apply A.

  (* Consider the class F {x} =  x *)
  remember (fun x => exists y, x = :(:{y}:,y):) as F eqn:EF.

  (* We claim that F is functional. *)
  assert (Functional F) as H2. {
    intros x y z H2 H3. rewrite EF in H2. rewrite EF in H3.
    destruct H2 as [u H2]. destruct H3 as [v H3].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H5].
    subst. apply Single.Charac. rewrite <- H3. apply Single.IsIn.
  }

  (* We claim that F[Singleton] = V. *)
  assert (F:[Singleton]: :~: V) as H3. {
    intros x. split; intros H3. 1: apply I. exists :{x}:. split.
    - exists x. reflexivity.
    - rewrite EF. exists x. reflexivity.
  }

  (* We obtain a contradiction by proving that V is small. *)
  apply VIsProper.

  (* So we need to prove that V is small. *)
  assert (Small V) as A. 2: apply A.

  (* Given the equality F[Singleton] = V. *)
  apply Small.EquivCompat with F:[Singleton]:. 1: assumption.

  (* We need to prove that F[Singleton] is small. *)
  assert (Small F:[Singleton]:) as A. 2: apply A.

  (* Which is true since F is functional, having assumed Singleton is small. *)
  apply Image.IsSmall; assumption.
Qed.

