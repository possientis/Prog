Require Import ZF.Axiom.Classic.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Relation.Charac.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Specify.

Module SRC := ZF.Set.Relation.Charac.

Definition fiber (f y:U) : U := {{ x :< domain f | fun x => f!x = y }}.

(* The fiber over y consists of the domain elements mapped to y.                *)
Proposition Charac : forall (f y x:U),
  x :< fiber f y <-> x :< domain f /\ f!x = y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f y x. apply (Specify.Charac (fun z => f!z = y) (domain f) x).
Qed.

(* A fiber is contained in the domain.                                          *)
Proposition IsIncl : forall (f y:U),
  fiber f y :<=: domain f.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f y. apply Specify.IsInclL.
Qed.

(* The fiber over one of a characteristic function is the marked subset.        *)
Proposition OfCharac : forall (a b:U),
  b :<=: a -> fiber (charac a b) :1: = b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1.
  assert (domain (charac a b) = a) as H2. { apply SRC.IsFun. }
  apply Incl.Double. split; intros x H3.
  (* Any element in the fiber lies in the domain, which is a.                   *)
  - apply Charac in H3. destruct H3 as [H3 H4]. rewrite H2 in H3.
    (* Outside b the characteristic function has value zero, not one.           *)
    assert (x :< b \/ ~ x :< b) as H5. { apply LawExcludedMiddle. }
    destruct H5 as [H5|H5]. 1: assumption.
    assert ((charac a b)!x = :0:) as H6. { apply SRC.EvalOut; assumption. }
    rewrite H6 in H4. exfalso. apply Natural.ZeroIsNotOne. assumption.
  (* Conversely, every marked element has characteristic value one.             *)
  - apply Charac. split.
    + rewrite H2. apply H1. assumption.
    + apply SRC.EvalIn. 2: assumption.
      apply H1. assumption.
Qed.

(* Binary-valued functions with the same fiber over one are equal.              *)
Proposition EqualOfOne : forall (a f g:U),
  Fun f a :2:               ->
  Fun g a :2:               ->
  fiber f :1: = fiber g :1: ->
  f = g.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a f g H1 H2 H3.
  apply Fun.Equal with a :2: a :2:; try assumption.
  - reflexivity.
  - intros x H4.
    assert (f!x :< :2:) as H5. { apply Fun.IsInRange with a; assumption. }
    assert (g!x :< :2:) as H6. { apply Fun.IsInRange with a; assumption. }
    assert (f!x = :0: \/ f!x = :1:) as H7. {
      rewrite Natural.TwoExtension in H5. apply Pair.Charac. assumption. }
    assert (g!x = :0: \/ g!x = :1:) as H8. {
      rewrite Natural.TwoExtension in H6. apply Pair.Charac. assumption. }
    destruct H7 as [H7|H7]; destruct H8 as [H8|H8].
    + rewrite H7, H8. reflexivity.
    + (* If g sends x to one, then x lies in the common fiber over one.         *)
      assert (x :< fiber g :1:) as H9. {
        apply Charac. split. 2: assumption.
        assert (domain g = a) as H9. { apply H2. }
        rewrite H9. assumption. }
      rewrite <- H3 in H9. apply Charac in H9. destruct H9 as [_ H9].
      rewrite H7 in H9. exfalso. apply Natural.ZeroIsNotOne. assumption.
    + (* If f sends x to one, then x lies in the common fiber over one.         *)
      assert (x :< fiber f :1:) as H9. {
        apply Charac. split. 2: assumption.
        assert (domain f = a) as H9. { apply H1. }
        rewrite H9. assumption. }
      rewrite H3 in H9. apply Charac in H9. destruct H9 as [_ H9].
      rewrite H8 in H9. exfalso. apply Natural.ZeroIsNotOne. assumption.
    + rewrite H7, H8. reflexivity.
Qed.
