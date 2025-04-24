Require Import ZF.Axiom.Foundation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Tuple.

(* No set belongs to itself.                                                    *)
Proposition NoElemLoop1 : forall x, ~ x :< x.
Proof.
  (* Let a be a set which belongs to itself *)
  intros a Ha.

  (* Consider the singleton set b = {a} *)
  remember :{a}: as b eqn:Hb.

  (* Then b is an non-empty set. *)
  assert (~ b = :0:) as H1. { rewrite Hb. apply SingletonIsNotEmpty. }

  (* From the foundation axiom, b has an element x such that x /\ b = 0 *)
  remember (Foundation b H1) as H2 eqn:A. clear A. destruct H2 as [x [H2 H3]].

  (* So x belongs to b *)
  assert (x :< b) as A. { apply H2. } clear A.

  (* And x /\ b = 0 *)
  assert (x :/\: b = :0:) as A. { apply H3. } clear A.

  (* Since x belongs to b = {a} we have x = a *)
  assert (x = a) as H4. { rewrite Hb in H2. apply SingleCharac in H2. apply H2. }

  (* Hence we have a /\ {a} = 0 *)
  subst. assert (a :/\: :{a}: = :0:) as A. { apply H3. } clear A.

  (* And since a :< a we see that a belongs to a /\ {a}, and so it belongs to 0 *)
  assert (a :< :0:) as H4.
    { rewrite <- H3. apply InterCharac. split.
      - apply Ha.
      - apply SingleIn.
    }

  (* This is our desired contradiction *)
  apply EmptyCharac in H4. contradiction.
Qed.

Proposition NoElemLoop2 : forall a b, ~ (a :< b /\ b :< a).
Proof.
  (* Let a,b be a sets such that a :< b and b :< a *)
  intros a b [Hab Hba].

  (* Consider the pair set c = {a,b} *)
  remember :{a,b}: as c eqn:Hc.

  (* Then c is an non-empty set. *)
  assert (~ c = :0:) as H1. { rewrite Hc. apply PairIsNotEmpty. }

  (* From the foundation axiom, c has an element x such that x /\ c = 0 *)
  remember (Foundation c H1) as H2 eqn:A. clear A. destruct H2 as [x [H2 H3]].

  (* So x belongs to c *)
  assert (x :< c) as A. { apply H2. } clear A.

  (* And x /\ c = 0 *)
  assert (x :/\: c = :0:) as A. { apply H3. } clear A.

  (* Since x belongs to c = {a,b} we have x = a or x = b *)
  assert (x = a \/ x = b) as H4. { rewrite Hc in H2. apply Pair.Charac in H2. apply H2. }

  (* We consider the case x = a and x = b separately *)
  destruct H4 as [H4|H4].

  (* When x = a, we have a /\ {a,b} = 0. But b belongs to both set, contradiction. *)
  - subst. assert (b :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply Hba.
        - apply Pair.InR.
      }
    apply EmptyCharac in H5. contradiction.

  (* When x = b, we have b /\ {a,b} = 0. But a belongs to both set, contradiction. *)
  - subst. assert (a :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply Hab.
        - apply Pair.InL.
      }
    apply EmptyCharac in H5. contradiction.
Qed.

Proposition NoElemLoop3 : forall a1 a2 a3, ~ (a1 :< a2 /\ a2 :< a3 /\ a3 :< a1).
Proof.
  (* Let a1 a2 a3 be a sets such that a1 :< a2, a2 :< a3 and a3 :< a1 *)
  intros a1 a2 a3 [H12 [H23 H31]].

  (* Consider the unordered tuple set a = {a1,a2,a3} *)
  remember :{a1,a2,a3}: as a eqn:Ha.

  (* Then a is an non-empty set. *)
  assert (~ a = :0:) as H1. { rewrite Ha. apply Tuple3IsNotEmpty. }

  (* From the foundation axiom, a has an element x such that x /\ a = 0 *)
  remember (Foundation a H1) as H2 eqn:A. clear A. destruct H2 as [x [H2 H3]].

  (* So x belongs to a *)
  assert (x :< a) as A. { apply H2. } clear A.

  (* And x /\ a = 0 *)
  assert (x :/\: a = :0:) as A. { apply H3. } clear A.

  (* Since x belongs to a = {a1,a2,a3} we have x = a1 or x = a2 or x = a3 *)
  assert (x = a1 \/ x = a2 \/ x = a3) as H4.
    { rewrite Ha in H2. apply Tuple3Charac in H2. apply H2. }

  (* We consider the cases x = a1,a2,a3 separately *)
  destruct H4 as [H4|[H4|H4]].

  (* When x = a1, we have a1 /\ {a1,a2,a3} = 0. But a3 belongs to both set *)
  - subst. assert (a3 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H31.
        - apply Tuple3In3.
      }
    apply EmptyCharac in H5. contradiction.

  (* When x = a2, we have a2 /\ {a1,a2,a3} = 0. But a1 belongs to both set *)
  - subst. assert (a1 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H12.
        - apply Tuple3In1.
      }
    apply EmptyCharac in H5. contradiction.

  (* When x = a3, we have a3 /\ {a1,a2,a3} = 0. But a2 belongs to both set *)
  - subst. assert (a2 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H23.
        - apply Tuple3In2.
      }
    apply EmptyCharac in H5. contradiction.
Qed.

Proposition NoElemLoop4 : forall a1 a2 a3 a4,
  ~ (a1 :< a2 /\ a2 :< a3 /\ a3 :< a4 /\ a4 :< a1).
Proof.
  (* Let a1 a2 a3 a4 be a sets such that a1 :< a2, a2 :< a3, a3 :< a4, a4 :< a1 *)
  intros a1 a2 a3 a4 [H12 [H23 [H34 H41]]].

  (* Consider the unordered tuple set a = {a1,a2,a3,a4} *)
  remember :{a1,a2,a3,a4}: as a eqn:Ha.

  (* Then a is an non-empty set. *)
  assert (~ a = :0:) as H1. { rewrite Ha. apply Tuple4IsNotEmpty. }

  (* From the foundation axiom, a has an element x such that x /\ a = 0 *)
  remember (Foundation a H1) as H2 eqn:A. clear A. destruct H2 as [x [H2 H3]].

  (* So x belongs to a *)
  assert (x :< a) as A. { apply H2. } clear A.

  (* And x /\ a = 0 *)
  assert (x :/\: a = :0:) as A. { apply H3. } clear A.

  (* Since x belongs to a = {a1,a2,a3,a4}, x must be a1,a2,a3 or a4 *)
  assert (x = a1 \/ x = a2 \/ x = a3 \/ x = a4) as H4.
    { rewrite Ha in H2. apply Tuple4Charac in H2. apply H2. }

  (* We consider the cases x = a1,a2,a3,a4 separately *)
  destruct H4 as [H4|[H4|[H4|H4]]].

  (* When x = a1, we have a1 /\ {a1,a2,a3,a4} = 0. But a4 belongs to both set *)
  - subst. assert (a4 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H41.
        - apply Tuple4In4.
      }
    apply EmptyCharac in H5. contradiction.

  (* When x = a2, we have a2 /\ {a1,a2,a3,a4} = 0. But a1 belongs to both set *)
  - subst. assert (a1 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H12.
        - apply Tuple4In1.
      }
    apply EmptyCharac in H5. contradiction.

  (* When x = a3, we have a3 /\ {a1,a2,a3,a4} = 0. But a2 belongs to both set *)
  - subst. assert (a2 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H23.
        - apply Tuple4In2.
      }
    apply EmptyCharac in H5. contradiction.

  (* When x = a4, we have a4 /\ {a1,a2,a3,a4} = 0. But a3 belongs to both set *)
  - subst. assert (a3 :< :0:) as H5.
      { rewrite <- H3. apply InterCharac. split.
        - apply H34.
        - apply Tuple4In3.
      }
    apply EmptyCharac in H5. contradiction.
Qed.
