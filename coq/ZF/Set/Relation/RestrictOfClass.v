Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Truncate.

Definition restrict (F:Class) (a:U) : U := truncate (F:|:toClass a).

(* Notation "F :|: a" := (restrict F a)                                         *)
Global Instance ClassPipe : Pipe Class U := { pipe := restrict }.

Proposition ToClass : forall (F:Class) (a:U),
  Class.Relation.Functional.Functional F ->
  toClass (F:|:a) :~: F:|:toClass a.
Proof.
  intros F a H1. apply Truncate.WhenSmall. apply Restrict.IsSmall.
  1: assumption. apply Small.SetIsSmall.
Qed.

Proposition ToClassWhenSmall : forall (F:Class) (a:U),
  Small F -> toClass (F:|:a) :~: F:|:toClass a.
Proof.
  intros F a H1. apply Truncate.WhenSmall, Restrict.IsSmall'. assumption.
Qed.

Proposition EquivCompat : forall (F G:Class) (a:U),
  F :~: G -> F:|:a = G:|:a.
Proof.
  intros F G a H1. apply Truncate.EquivCompat, Restrict.EquivCompatL. assumption.
Qed.

Proposition Charac : forall (F:Class) (a x:U),
  Class.Relation.Functional.Functional F ->
  x :< F:|:a                             ->
  exists y z, x = :(y,z): /\ y :< a /\ F :(y,z):.
Proof.
  intros F a x H1 H2. apply ToClass in H2. 2: assumption.
  destruct H2 as [y [z H2]]. exists y. exists z. assumption.
Qed.

Proposition CharacRev : forall (F:Class) (a x y z:U),
  Class.Relation.Functional.Functional F ->
  x = :(y,z):                            ->
  y :< a                                 ->
  F :(y,z):                              ->
  x :< F:|:a.
Proof.
  intros F a x y z H1 H2 H3 H4. apply ToClass. 1: assumption.
  exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (F:Class) (a y z:U),
  Class.Relation.Functional.Functional F ->
  :(y,z): :< (F:|:a)                     ->
  y :< a /\ F :(y,z):.
Proof.
  intros F a y z H1 H2. apply Charac in H2. destruct H2 as [y' [z' [H2 [H3 H4]]]].
  apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H5]. subst. 2: assumption.
  split; assumption.
Qed.

Proposition Charac2Rev : forall (F:Class) (a y z:U),
  Class.Relation.Functional.Functional F ->
  y :< a                                 ->
  F :(y,z):                              ->
  :(y,z): :< (F:|:a).
Proof.
  intros F a y z H1 H2 H3. apply CharacRev with y z; try assumption. reflexivity.
Qed.

Proposition IsRelation : forall (F:Class) (a:U),
  Class.Relation.Functional.Functional F ->
  Relation (F:|:a).
Proof.
  intros F a H1 x H2. apply Charac in H2. 2: assumption.
  destruct H2 as [y [z [H2 _]]]. exists y. exists z. assumption.
Qed.

Proposition IsFunctional : forall (F:Class) (a:U),
  Class.Relation.Functional.Functional F        ->
  ZF.Set.Relation.Functional.Functional (F:|:a).
Proof.
Admitted.
