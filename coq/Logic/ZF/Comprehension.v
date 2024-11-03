Declare Scope ZF_Comprehension_scope.
Open    Scope ZF_Comprehension_scope.

Require Import Logic.ZF.Class.
Require Import Logic.ZF.ClassRel.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Replacement.

(* Given a set theoretic predicate P and a set a, there exists a set b whose    *)
(* elements are the elements of the set a which satisfy P.                      *)
(* This is a theorem and not an axiom as it can be derived from replacement.    *)
Theorem Comprehension : forall (P:U -> Prop),
  forall a, exists b, forall x, x :< b <-> x :< a /\ P x.
Proof.
  (* Let P be a predicate and a be a set. *)
  intros P a.

  (* Consider the class relation F x y := P x /\ x = y. *)
  remember (fun x y => P x /\ x = y) as F eqn:H1.

  (* We claim that this class relation is functional. *)
  assert (Functional F) as H2.
    { intros x y z H3 H4. rewrite H1 in H3. rewrite H1 in H4.
      destruct H3 as [_ H3]. destruct H4 as [_ H4]. subst.
      reflexivity.
    }

  (* We claim that the class F[a] (direct image of the set a by F) is the same  *)
  (* as the class fun x => x :< a /\ P x.                                       *)
  assert (forall x, F[a] x <-> x :< a /\ P x) as H3.
    { rewrite H1. unfold Image. intros x. split; intros H4.
      - destruct H4 as [y [H5 [H6 H7]]]. subst. auto.
      - exists x. split.
        + destruct H4 as [H4 _]. apply H4.
        + split. 2: reflexivity. destruct H4 as [_ H4]. apply H4.
    }

  (* We need to show the existence of b such that x :< b <-> x :< a /\ P x.*)
  assert (exists b, forall x, x :< b <-> x :< a /\ P x) as A. 2: apply A.

  (* Let us take b to be the direct image of a by the functional relation F     *)
  (* which is a small class and can be viewed as a set.                         *)
  exists (replaceSet F a H2).

  (* We need to show x :< b <-> x :< a /\ P x *)
  assert (forall x, x :< (replaceSet F a H2) <-> x :< a /\ P x) as A. 2: apply A.

  intros x. split.

  (* Proof of -> *)
  - assert (x :< (replaceSet F a H2) -> x :< a /\ P x) as A. 2: apply A.
    intros H4. apply ReplaceCharac, H3 in H4. apply H4.

  (* Proof of <- *)
  - assert (x :< a /\ P x -> x :< (replaceSet F a H2)) as A. 2: apply A.
    intros H4. apply ReplaceCharac, H3. apply H4.
Qed.

(* It is useful to define the predicate underlying the comprehension axiom.     *)
Definition CompPred (P:U -> Prop) (a:U) : U -> Prop := fun x =>
  x :< a /\ P x.

(* The comprehension predicate of a and P is small                              *)
Proposition CompSmall : forall (P:U -> Prop) (a:U),
    Small (CompPred P a).
Proof.
  apply Comprehension.
Qed.

(* We consider the set defined by the comprehension predicate of P and a.       *)
Definition compSet (P:U -> Prop) (a:U) : U
  := toSet (CompPred P a) (CompSmall P a).

Notation ":{ a | P }:" := (compSet P a)
  (at level 1, no associativity) : ZF_Comprehension_scope.

(* Characterisation of the elements of {a :| P}.                                *)
Proposition CompCharac : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: <-> x :< a /\ P x.
Proof.
  unfold compSet. intros P a. apply ClassCharac.
Qed.

(* Every element of the comprehension set of P and a is an element of a.        *)
Proposition CompInInA : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: -> x :< a.
Proof.
  intros P a x H1. apply CompCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

(* Every element of the comprehension set of P and a satisfies the predicate P. *)
Proposition CompInP : forall (P:U -> Prop) (a:U),
  forall x, x :< :{a | P}: -> P x.
Proof.
  intros P a x H1. apply CompCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

(* If a set belongs to a set a and satisfies the predicate P, then it belongs   *)
(* to the comprehension set of P and a.                                         *)
Proposition CompInAPIn: forall (P:U -> Prop) (a:U),
  forall x, x :< a -> P x -> x :< :{a | P}:.
Proof.
  intros P a x H1 H2. apply CompCharac. split; assumption.
Qed.

