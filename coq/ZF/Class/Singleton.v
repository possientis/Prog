Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Singleton.

(* The class of all singletons.                                                 *)
Definition Singleton : Class := fun x => exists y, x = :{y}:.

Proposition SingletonIsProper : Proper Singleton.
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
    apply OrdPairEqual in H2. destruct H2 as [H2 H4].
    apply OrdPairEqual in H3. destruct H3 as [H3 H5].
    subst. apply SingleCharac. rewrite <- H3. apply SingleIn.
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
  apply SmallEquivCompat with F:[Singleton]:. 1: assumption.

  (* We need to prove that F[Singleton] is small. *)
  assert (Small F:[Singleton]:) as A. 2: apply A.

  (* Which is true since F is functional, having assumed Singleton is small. *)
  apply ImageIsSmall; assumption.
Qed.

