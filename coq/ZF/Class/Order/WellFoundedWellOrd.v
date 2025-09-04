Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a well-founded well-ordering on A.   *)
Definition WellFoundedWellOrd (R A:Class) : Prop :=
  WellFounded R A /\ WellOrdering R A.

Proposition WhenIncl : forall (R A B:Class),
  WellFoundedWellOrd R A -> B :<=: A -> WellFoundedWellOrd R B.
Proof.
  intros R A B [H1 H2] H3. split.
  - apply WellFounded.WhenIncl with A; assumption.
  - apply WellOrdering.WhenIncl with A; assumption.
Qed.

Proposition IsIrreflexive : forall (R A:Class),
  WellFoundedWellOrd R A -> Irreflexive R A.
Proof.
  intros R A H1. apply WellOrdering.IsIrreflexive, H1.
Qed.

Proposition IsTransitive : forall (R A:Class),
  WellFoundedWellOrd R A -> Transitive R A.
Proof.
  intros R A H1. apply WellOrdering.IsTransitive, H1.
Qed.

(* If R is a wfwo on A, every non-empty subclass of A has an R-minimal element. *)
Proposition HasMinimal : forall (R A B:Class),
  WellFoundedWellOrd R A ->
  B :<=: A               ->
  B :<>: :0:             ->
  exists x, Minimal R B x.
Proof.

  (* Let R A B be arbitrary classes. *)
  intros R A B.

  (* We assume that R is a well-founded well-ordering on A. *)
  intros [H1 H2].

  (* In perticular, R is well-founded on A. *)
  assert (WellFounded R A) as X. apply H1. clear X.

  (* And R is a well-ordering on A. *)
  assert (WellOrdering R A) as X. apply H2. clear X.

  (* We assume that B is a subclass of A. *)
  intros H3. assert (B :<=: A) as X. apply H3. clear X.

  (* We assume that B is a non-empty class. *)
  intros H4. assert (~ B :~: :0:) as X. apply H4. clear X.

  (* We need to show that B has an R-minimal element. *)
  assert (exists x, Minimal R B x) as X. 2: apply X.

  (* Being non-empty, B has an element, *)
  apply Class.Empty.HasElem in H4.

  (* Let b be such an element of B. *)
  destruct H4 as [b H4]. assert (B b) as X. apply H4. clear X.

  (* Let C be the initital segment of R in B at b. *)
  remember (initSegment R B b) as C eqn:EC.

  (* Either C is an empty class or it is not. *)
  assert (C :~: :0: \/ ~ C :~: :0:) as H5. apply LawExcludedMiddle.

  (* We shall consider these two cases separately. *)
  destruct H5 as [H5|H5].

  (* We first assume that C is empty. *)
  - assert (C :~: :0:) as X. apply H5. clear X.

  (* We claim that b is our desired minimal element. *)
    exists b.

  (* So we need to prove that b in R-minimal in B. *)
    assert (Minimal R B b) as X. 2: apply X.
    apply Minimal.EmptySegment. split.

  (* Which follows from the fact that b lies in B. *)
    + assert (B b) as X. 2: apply X. assumption.

  (* And that the initial segment at b in B is empty. *)
    + assert (initSegment R B b :~: :0:) as X. 2: apply X.
      rewrite <- EC. assumption.

  (* So we now assume that C is an non-empty class. *)
  - assert (~ C :~: :0:) as X. apply H5. clear X.

  (* R being well-founded on A, it is well-founded on B. *)
    assert (WellFounded R B) as H6. {
      apply WellFounded.WhenIncl with A; assumption.
    }

  (* And furthermore C is a small class. *)
    assert (Small C) as H7. { rewrite EC. apply H6. assumption. }

  (* Let c be the set defined by the class C. *)
    remember (fromClass C H7) as c eqn:Ec.

  (* Then we have toClass c = C. *)
    assert (toClass c :~: C) as H8. { rewrite Ec. apply ToFromClass. }

  (* Furthermore, the set c is not empty. *)
    assert (c <> :0:) as H9. {
      intros H9. apply H5. apply Equiv.Tran with (toClass c).
      - apply Equiv.Sym. assumption.
      - apply EmptyToClass. assumption.
    }

  (* So c is a non-empty subset of the class B. *)
    assert (toClass c :<=: B) as H10. {
      apply Incl.EquivCompatL with C.
      - apply Equiv.Sym. assumption.
      - rewrite EC. apply InitSegment.IsIncl.
   }

  (* R being well-founded on B, it follows that c has an R-minimal element. *)
    assert (exists x, Minimal R (toClass c) x) as H11. {
      apply H6; assumption.
    }

  (* So let x be such an R-minimal element in c. *)
    destruct H11 as [x H11].
    assert (Minimal R (toClass c) x) as X. apply H11. clear X.

  (* We claim that x is our desired R-minimal element of B. *)
    exists x.

  (* So we need to prove that x is an R-minimal element in B. *)
    assert (Minimal R B x) as X. 2: apply X. split.

  (* We first need to show that x lies in B. *)
    + assert (B x) as X. 2: apply X.
      apply H10. apply Minimal.IsIn with R. assumption.

  (* And furthermore than no y in B is 'less' than x. *)
    + assert (forall y, B y -> ~ R :(y,x):) as X. 2: apply X.

  (* So let y be an element of B. *)
      intros y H12. assert (B y) as X. apply H12. clear X.

  (* We need to show that y is not 'less' than x. *)
      assert (~ R :(y,x):) as X. 2: apply X.

  (* But if y is less than x, by transitivity it is less than b. *)
      intros H13. assert (R :(y,b):) as H14. {
        apply WellOrdering.IsTransitive in H2. apply H2 with x.
        - apply H3. assumption.
        - apply H3, H10, Minimal.IsIn with R. assumption.
        - apply H3. assumption.
        - assumption.
        - apply InitSegment.IsLess with B.
          assert (initSegment R B b x) as X. 2: apply X.
          rewrite <- EC. apply H8, Minimal.IsIn with R. assumption.
      }

  (* So y is actually part of the initial segment of R in B at b which is C. *)
      assert (C y) as H15. {
        rewrite EC. apply InitSegment.Charac. split; assumption.
      }

  (* This contradicts the R-minimality of x in c. *)
      assert (~ R :(y,x):) as H16. 2: contradiction.
      apply Minimal.NotLess with (toClass c). 2: assumption.
      apply H8. assumption.
Qed.

