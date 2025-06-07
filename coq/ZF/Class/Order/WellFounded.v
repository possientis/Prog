Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Singleton.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Single.

(* Predicate expressing the fact that R is a well-founded class on A. R is well *)
(* founded on A iff it is founded on A and all initial segments are small.      *)
Definition WellFounded (R A:Class) : Prop :=
  Founded R A /\ forall (a:U), A a -> Small (initSegment R A a).

(* If R is founded on a small class A, then it is well-founded on A.            *)
Proposition WellFoundedWhenFoundedOnSmall : forall (R A:Class),
  Founded R A -> Small A -> WellFounded R A.
Proof.
  intros R A H1 H2. split. 1: assumption. intros a H3.
  apply InclInSmallIsSmall with A. 2: assumption. apply InitSegment.IsIncl.
Qed.

(* If R is founded on a set a, then it is well-founded on a.                    *)
Proposition WellFoundedWhenFoundedOnSet : forall (R:Class) (a:U),
  Founded R (toClass a) -> WellFounded R (toClass a).
Proof.
  intros R a H1. apply WellFoundedWhenFoundedOnSmall. 1: assumption.
  apply SetIsSmall.
Qed.

(* If R is well-founded on A superclass of B, then it is well-founded on B.     *)
Proposition WellFoundedIncl : forall (R A B:Class),
  WellFounded R A -> B :<=: A -> WellFounded R B.
Proof.
  intros R A B [H1 H2] H3. split.
  - apply FoundedIncl with A; assumption.
  - intros a H4. apply InclInSmallIsSmall with (initSegment R A a).
    + apply InitSegment.InclCompatR. assumption.
    + apply H2, H3. assumption.
Qed.

Proposition WellFoundedIsom : forall (F R S A B: Class),
  Isom F R S A B -> WellFounded R A <-> WellFounded S B.
Proof.
  (* It is sufficient to prove -> *)
  assert (forall (F R S A B:Class),
    Isom F R S A B -> WellFounded R A -> WellFounded S B) as L. {
    intros F R S A B H1 [H2 H3]. assert (H4 := H1). destruct H4 as [H4 _]. split.
    - apply (FoundedIsom F R S A B); assumption.
    - intros b H5. remember (F^:-1:!b) as a eqn:H6.
      assert (b = F!a) as H7. { rewrite H6. symmetry.
        apply Bij.EvalOfConverseEval with A B; assumption. }
      assert (A a) as H8. { rewrite H6. apply Bij.ConverseEvalIsInDomain with B; assumption. }
      rewrite H7. apply Small.EquivCompat with F:[initSegment R A a]:.
      + apply InitSegment.IsomFullImage; assumption.
      + apply Bij.ImageIsSmall with A B. 1: assumption. apply H3. assumption. }

  (* The proof of the equivalence follows. *)
  intros F R S A B H1. split.
  - apply L with F. assumption.
  - apply L with F^:-1:, ConverseIsIsom. assumption.
Qed.

(* R can be founded for A, but not well-founded for A.                          *)
Proposition WellFoundedCanFailWhenFounded : exists (R A:Class),
  Founded R A /\ ~ WellFounded R A.
Proof.
  (* Let A be the class of all singletons and pairs. *)
  remember (fun x =>
     (exists y, x = :{y}:) \/ (exists y z, y <> z /\ x = :{y,z}:)) as A eqn:EA.

  (* Let R be the class (relation) 'has fewer elements'. *)
  remember (fun x => exists y z, x = :(y,z): /\
    (exists u, y = :{u}:) /\ (exists v w, v <> w /\ z = :{v,w}:)) as R eqn:ER.

  (* We claim that R and A satisfy the desired property. *)
  exists R. exists A. split.

  (* We first need to show that R is founded on A. *)
  - assert (Founded R A) as X. 2: apply X.

    (* Let a be a non-empty set which is a subclass of A. *)
    intros a H1 H2.

    (* Then a is a subclass of A. *)
    assert (toClass a :<=: A) as X. apply H1. clear X.

    (* And a is not empty. *)
    assert (a <> :0:) as X. apply H2. clear X.

    (* We need to show that a as an R-minimal element, *)
    assert (exists x, Minimal R (toClass a) x) as X. 2: apply X.

    (* We will consider two cases depending on whether a contains a singleton. *)
    assert ((exists x, :{x}: :< a) \/ ~ (exists x, :{x}: :< a)) as H3.
    apply LawExcludedMiddle. destruct H3 as [H3|H3].

    (* We first assume that a contains a singleton *)
    + assert (exists x, :{x}: :< a) as X. apply H3. clear X.

      (* So let x be such that {x} belongs to a. *)
      destruct H3 as [x H3]. assert (:{x}: :< a) as X. apply H3. clear X.

      (* We claim that {x} is a desired R-minimal element of a. *)
      exists :{x}:.

      (* So we need to show this is the case. *)
      assert (Minimal R (toClass a) :{x}:) as X. 2: apply X.

      apply Minimal.Suffice. 1: assumption. intros b H4 H5.
      rewrite ER in H5. destruct H5 as [y [z [H5 [_ H6]]]].
      apply OrdPair.WhenEqual in H5. destruct H5 as [_ H5]. subst.
      destruct H6 as [v [w [H6 H7]]]. revert H7.
      apply IsNotPair. assumption.

    (* We now assume that a contains no singleton. *)
    + assert (~exists x, :{x}: :< a) as X. apply H3. clear X.

      (* Let y z be such that {y,z} belongs to a and y <> z. *)
      apply HasElem in H2. destruct H2 as [x H2].
      assert (H4 := H2). apply H1 in H4. rewrite EA in H4.
      destruct H4 as [H4|H4]. 1: {
        destruct H4 as [y H4]. rewrite H4 in H2. exfalso. apply H3.
        exists y. assumption.
      }
      destruct H4 as [y [z [H4 H5]]]. rewrite H5 in H2.

      (* Then {y,z} belongs to a. *)
      assert (:{y,z}: :< a) as X. apply H2. clear X.

      (* And y <> z. *)
      assert (y <> z) as X. apply H4. clear X.

      (* We claim that {y,z} is a desired R-minimal elemen of a. *)
      exists :{y,z}:.

      (* So we need to show this is the case. *)
      assert (Minimal R (toClass a) :{y,z}:) as X. 2: apply X.

      apply Minimal.Suffice. 1: assumption. intros b H6 H7.
      rewrite ER in H7. destruct H7 as [c [d [H7 [H8 _]]]].
      apply OrdPair.WhenEqual in H7. destruct H7 as [H7 _]. subst.
      destruct H8 as [u H8]. subst. apply H3. exists u. assumption.

  (* We now need to show that R is not well-founded on A. *)
  - assert (~ WellFounded R A) as X. 2: apply X.

    (* So let us assume that it is. *)
    intros H1. assert (WellFounded R A) as X. apply H1. clear X.

    (* In particular all initial segments of R in A are small. *)
    destruct H1 as [_ H1].
    assert (forall a, A a -> Small (initSegment R A a)) as X. apply H1. clear X.

    (* Consider the set a = {0,{0}}. *)
    remember :{:0:,:{:0:}:}: as a eqn:Ea.

    (* Then a is an element of A. *)
    assert (A a) as H2. { rewrite EA. right. exists :0:. exists :{:0:}:.
      split. 2: assumption. intros H2. apply SingletonIsNotEmpty with :0:.
      symmetry. assumption.
    }

    (* And the initial segment of R in A at a is the class of all singletons. *)
    assert (initSegment R A a :~: Singleton) as H3. { intros x. split; intros H3.
      - apply InitSegment.Charac in H3. destruct H3 as [_ H3]. rewrite ER in H3.
        destruct H3 as [y [z [H3 [[u H4] _]]]]. apply OrdPair.WhenEqual in H3.
        destruct H3 as [H3 _]. subst. exists u. reflexivity.
      - destruct H3 as [u H3]. apply InitSegment.Charac. split.
        + rewrite H3, EA. left. exists u. reflexivity.
        + rewrite ER. exists :{u}:. exists a. split.
          * rewrite H3. reflexivity.
          * split. { exists u. reflexivity. } {
              exists :0:. exists :{:0:}:. split. 2: assumption.
              intros H4. apply SingletonIsNotEmpty with :0:. symmetry. assumption.
            }
    }

    (* We obtain a contradiction by showing the class of singletons is small.   *)
    apply Singleton.IsProper.

    (* So we need to show that the class of singletons is small.                *)
    assert (Small Singleton) as X. 2: apply X.

    (* Given that this class coincide with the initial segment at a...          *)
    apply Small.EquivCompat with (initSegment R A a). 1: assumption.

    (* We simply need to show the initial segment at a is small.                *)
    assert (Small (initSegment R A a)) as X. 2: apply X.

    (* Which is a consequence of our well-foundedness assumption.               *)
    apply H1; assumption.
Qed.

