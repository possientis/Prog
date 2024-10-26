Declare Scope ZF_Axioms_scope.
Open Scope ZF_Axioms_scope.

(* There is a universe of sets                                                  *)
Axiom U : Type.

(* There is a fundamental membership predicate between sets                     *)
Axiom Elem : U -> U -> Prop.

Notation "x :< y" := (Elem x y)
  (at level 1, no associativity)      : ZF_Axioms_scope.

(* Predicate over predicates, expressing the fact that at least one set         *)
(* satisfies the given predicate.                                               *)
Definition Exists (P:U -> Prop) : Prop := exists x, P x.

(* Predicate over predicates, expressing the fact that no more than one set     *)
(* satisfies the given predicate.                                               *)
Definition Unique (P:U -> Prop) : Prop := forall a b, P a -> P b -> a = b.

(* When a predicate is satisfied by a unique set, we can give it a name.        *)
Axiom Skolem : forall (P:U -> Prop), Exists P -> Unique P -> U.

Arguments Skolem {P}.

(* The set named by the Skolem axiom does satisfy the defining predicate.       *)
Axiom Skolem_satisfy: forall (P:U -> Prop) (p:Exists P) (q:Unique P), P(Skolem p q).

(* If a set satifies the defining predicate, then it is equal to the Skolem set *)
Proposition Skolem_charac : forall (P:U -> Prop) (p:Exists P) (q:Unique P),
  forall x, P x -> x = Skolem p q.
Proof.
  intros P p q x Hx. apply q.
  - apply Hx.
  - apply Skolem_satisfy.
Qed.

(* The Skolem set associated with a predicate is the same regardless of proofs. *)
Proposition Skolem_proof : forall (P:U -> Prop) (p p':Exists P) (q q':Unique P),
  Skolem p q = Skolem p' q'.
Proof.
  intros P p p' q q'. apply Skolem_charac, Skolem_satisfy.
Qed.

(* If two sets have the same elements, then they are equal                      *)
Axiom Extensionality : forall a b, (forall x, x :< a <-> x :< b) -> a = b.

(* If two sets are characterised by the same predicate, then they are equal.    *)
Proposition unique_charac : forall (P:U -> Prop), forall a b,
  (forall x, x :< a <-> P x) ->
  (forall x, x :< b <-> P x) ->
  a = b.
Proof.
  intros P a b Ha Hb. apply Extensionality. intros x. split.
  - intros H. apply Hb, Ha, H.
  - intros H. apply Ha, Hb, H.
Qed.

(* Given a predicate P and a set a, there exists a set b whose elements are the *)
(* elements of a satisfying P.                                                  *)
Axiom Comprehension : forall (P:U -> Prop),
  forall a, exists b, forall x, x :< b <-> x :< a /\ P x.

(* It is useful to define the predicate underlying the comprehension axiom      *)
Definition Comp_pred (P:U -> Prop) (a:U) : U -> Prop := fun b =>
  forall x, x :< b <-> x :< a /\ P x.

(* The comprehension predicate of P and a is satisfied by at least one set .    *)
Proposition Comp_exists: forall (P:U -> Prop) (a:U),
    Exists (Comp_pred P a).
Proof.
  intros P a. apply Comprehension.
Qed.

(* The comprehension predicate of P and a is satisfied by no more than one set. *)
Proposition Comp_unique: forall (P:U -> Prop) (a:U),
    Unique (Comp_pred P a).
Proof.
  intros P a. unfold Unique. apply unique_charac.
Qed.

(* It is convenient to define the set referred to by the comprehension axiom.   *)
Definition Comp_set (P:U -> Prop) (a:U) : U
  := Skolem (Comp_exists P a) (Comp_unique P a).

(* The comprehension set of P a satisfies the comprehension predicate of P a.   *)
Proposition Comp_satisfy : forall (P:U -> Prop) (a:U),
  Comp_pred P a (Comp_set P a).
Proof.
  intros P a. unfold Comp_set. apply Skolem_satisfy.
Qed.

(* Characterisation of the elements of the comprehension set of P and a.        *)
Proposition Comp_charac : forall (P:U -> Prop) (a:U),
  forall x, x :< (Comp_set P a) <-> x :< a /\ P x.
Proof.
  apply Comp_satisfy.
Qed.

(* Every element of the comprehension set of P a is an element of a.            *)
Proposition Comp_a : forall (P:U -> Prop) (a:U),
  forall x, x :< (Comp_set P a) -> x :< a.
Proof.
  intros P a x Hx.
  assert (Comp_pred P a (Comp_set P a)) as H.
    { apply Comp_satisfy. }
  unfold Comp_pred in H.
  apply H in Hx. destruct Hx as [H1 H2].
  apply H1.
Qed.

(* Every element of the comprehension set of P a satisfies the predicate P.     *)
Proposition Comp_P : forall (P:U -> Prop) (a:U),
  forall x, x :< (Comp_set P a) -> P x.
Proof.
  intros P a x Hx.
  assert (Comp_pred P a (Comp_set P a)) as H.
    { apply Comp_satisfy. }
  unfold Comp_pred in H.
  apply H in Hx. destruct Hx as [H1 H2].
  apply H2.
Qed.

(* If a set belongs to a and satisfies P, it belongs to the comprehension set   *)
Proposition Comp_in: forall (P:U -> Prop) (a:U),
  forall x, x :< a -> P x -> x :< (Comp_set P a).
Proof.
  intros P a x H1 H2.
  assert (Comp_pred P a (Comp_set P a)) as H.
    { apply Comp_satisfy. }
  unfold Comp_pred in H. apply H.
  split.
    - apply H1.
    - apply H2.
Qed.

(* There exists no set containing all sets                                      *)
Proposition Russell : ~ exists a, forall x, x :< a.
Proof.
  (* Let a be a set containing all sets *)
  intros [a Ha].

  (* Consider the predicate P x = ~ x :< x *)
  remember (fun x => ~ x :< x) as P eqn:E.

  (* Consider the set b of all x in a which do not belong to themselves *)
  remember (Comp_set P a) as b eqn:E'.

  (* We claim that b does not belong to itself *)
  assert (~ b :< b) as H1.
    { intro H2.
      assert (P b) as H3.
        { apply Comp_P with a. rewrite <- E'. apply H2.
        }
      rewrite E in H3.
      contradiction.
    }

  (* We claim that b does belong to itself *)
  assert (b :< b) as H2.
    { rewrite E'. apply Comp_in; rewrite <- E'.
      - apply Ha.
      - rewrite E. apply H1.
    }

  (* We have obtained a contradiction *)
  contradiction.
Qed.
