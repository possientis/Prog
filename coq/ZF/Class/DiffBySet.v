Require Import ZF.Class.Diff.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Union2.
Require Import ZF.Set.Relation.ImageUnderClass.

Export ZF.Notation.Diff.

Definition diff (A:Class) (a:U) : Class := A :\: toClass a.

(* Notation "A :\: a" := (diff A a)                                             *)
Global Instance ClassDiffBySet : Diff Class U := { diff := diff }.

(* An element is in A minus a iff it is in A and not a member of a.             *)
Proposition Charac : forall (A:Class) (a:U) (x:U),
  (A :\: a) x <-> A x /\ ~ x :< a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a x. split; intros H1.
  - destruct H1 as [H1 H2]. split. 1: assumption.
    intros H3. apply H2. apply H3.
  - destruct H1 as [H1 H2]. split. 1: assumption.
    intros H3. apply H2. apply H3.
Qed.

(* The class-by-set difference is compatible with class equivalence.            *)
Proposition EquivCompat : forall (A B:Class) (a:U),
  A :~: B -> A :\: a :~: B :\: a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A B a H1. apply Class.Diff.EquivCompatL. assumption.
Qed.

(* The class-by-set difference is compatible with class inclusion.              *)
Proposition InclCompatL : forall (A B:Class) (a:U),
  A :<=: B -> A :\: a :<=: B :\: a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A B a H1. apply Class.Diff.InclCompatL. assumption.
Qed.

(* When b is a subset of c, A minus c is included in A minus b.                 *)
Proposition InclCompatR : forall (A:Class) (b c:U),
  b :<=: c -> A :\: c :<=: A :\: b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A b c H1. apply Class.Diff.InclCompatR. assumption.
Qed.

(* The class-by-set difference is included in the original class.               *)
Proposition IsInclL : forall (A:Class) (a:U),
  A :\: a :<=: A.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a. apply Class.Diff.IsInclL.
Qed.

(* The class-by-set difference is included in the complement of the set.        *)
Proposition IsInclR : forall (A:Class) (a:U),
  A :\: a :<=: :¬: toClass a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a. apply Class.Diff.IsInclR.
Qed.

(* Removing the empty set from A leaves A unchanged.                            *)
Proposition IdentityR : forall (A:Class), A :\: :0: :~: A.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Nothing belongs to the empty set, so no element of A is removed.           *)
  intros A x. split; intros H1.
  - apply Class.Diff.IsInclL in H1. assumption.
  - split. 1: assumption. apply Empty.NoElem.
Qed.

(* The class-by-set difference of a small class is small.                       *)
Proposition IsSmall : forall (A:Class) (a:U),
  Small A -> Small (A :\: a).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a H1. apply Class.Diff.IsSmall. assumption.
Qed.

(* The class-by-set difference of a proper class is proper.                     *)
Proposition IsProper : forall (A:Class) (a:U),
  Proper A -> Proper (A :\: a).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a H1. apply Class.Diff.IsProper. assumption.
Qed.

(* The difference A minus a is empty iff A is included in the class of a.       *)
Proposition WhenZero : forall (A:Class) (a:U),
  A :\: a :~: :0: <-> A :<=: toClass a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a. apply Class.Diff.WhenZero.
Qed.

(* If the difference is non-empty, A is not equivalent to the class of a.       *)
Proposition WhenNotEmpty : forall (A:Class) (a:U),
  A :\: a :<>: :0: -> A :<>: toClass a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a H1. apply Class.Diff.WhenNotEmpty. assumption.
Qed.

Proposition WhenIncl : forall (A:Class) (a:U),
  toClass a :<=: A -> A :\: a :<>: :0: <-> A :<>: toClass a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a H1. apply Class.Diff.WhenIncl. assumption.
Qed.

(* If the class of a is properly included in A, the difference is non-empty.    *)
Proposition WhenLess : forall (A:Class) (a:U),
  toClass a :<: A -> A :\: a :<>: :0:.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A a H1. apply Class.Diff.WhenLess. assumption.
Qed.

(* The difference distributes over set union on the right.                      *)
Proposition UnionR : forall (A:Class) (b c:U),
  A :\: (b:\/:c) :~: A:\:b :/\: A:\:c.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros A b c x. split; intros H1.
  - (* x is in A but not in b union c, so x is in both A\b and A\c              *)
    apply Charac in H1. destruct H1 as [H1 H2]. split.
    + apply Charac. split. 1: assumption.
      intros H3. apply H2. apply Union2.Charac. left. assumption.
    + apply Charac. split. 1: assumption.
      intros H3. apply H2. apply Union2.Charac. right. assumption.
  - (* x is in both A\b and A\c, so x is in A and not in b union c              *)
    destruct H1 as [H1 H2].
    apply Charac in H1. destruct H1 as [H1 H3].
    apply Charac in H2. destruct H2 as [_ H4].
    apply Charac. split. 1: assumption.
    intros H5. apply Union2.Charac in H5.
    destruct H5 as [H5|H5]; contradiction.
Qed.

(* The image of A minus a under injective functional F equals F[A] minus F[a].  *)
Proposition Image : forall (F A:Class) (a:U),
  Functional F^:-1: -> Functional F -> F:[A:\:a]: :~: F:[A]: :\: F:[a]:.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* The class image of A minus a is connected to the set image via ToClass.    *)
  intros F A a H1 H2.
  apply Equiv.Tran with (F:[A]: :\: F:[toClass a]:).
  - apply Class.Diff.Image. assumption.
  - apply Class.Diff.EquivCompatR. apply Equiv.Sym. apply ImageUnderClass.ToClass.
    assumption.
Qed.

