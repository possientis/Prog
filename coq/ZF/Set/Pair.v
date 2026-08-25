Declare Scope ZF_Set_Pair_scope.
Open    Scope ZF_Set_Pair_scope.

Require Import ZF.Axiom.Define.
Require Import ZF.Axiom.Pairing.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.

(* Predicate saying that a set contains exactly a and b.                        *)
Definition IsPairOf (a b:U) : Class := fun x =>
  forall y, y :< x <-> y = a \/ y = b.

(* The pairing axiom gives a set containing exactly a and b.                    *)
Proposition Exists : forall (a b:U), Define.Exists (IsPairOf a b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. apply Pairing.
Qed.

(* A set containing exactly a and b is unique.                                  *)
Proposition Unique : forall (a b:U), Define.Unique (IsPairOf a b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d H1 H2. apply EqualToClass. intros x. split; intros H3.
  - apply H2, H1, H3.
  - apply H1, H2, H3.
Qed.

(* We consider the set containing exactly a and b.                              *)
Definition pair (a b:U) : U :=
  define (IsPairOf a b) (Exists a b) (Unique a b).

Notation ":{ a , b }:" := (pair a b)
  (at level 1, no associativity) : ZF_Set_Pair_scope.

(* A set x belongs to {a,b} iff x = a or x = b.                                 *)
Proposition Charac : forall (a b:U),
  forall x, x :< :{a,b}: <-> x = a \/ x = b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. unfold pair. apply Define.IsIn.
Qed.

(* The set a is an element of the set {a,b}.                                    *)
Proposition IsInL : forall (a b:U), a :< :{a,b}:.
Proof.
  intros a b. apply Charac. left. reflexivity.
Qed.

(* The set b is an element of the set {a,b}.                                    *)
Proposition IsInR : forall (a b:U), b :< :{a,b}:.
Proof.
  intros a b. apply Charac. right. reflexivity.
Qed.

(* A contains both a and b iff the class of {a,b} is a subclass of A.           *)
Proposition ToClassIncl : forall (A:Class) (a b:U),
  A a /\ A b <-> toClass :{a,b}: :<=: A.
Proof.
  intros A a b. split; intros H1.
  - destruct H1 as [H1 H2]. intros x H3. apply Charac in H3.
    destruct H3 as [H3|H3]; subst; assumption.
  - split; apply H1.
    + apply IsInL.
    + apply IsInR.
Qed.

