Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Specify.

Export ZF.Notation.InfAbove.

(* The infimum of the set a.                                                    *)
Definition inf (a:U) : U := :I( :{ a | Ordinal }: ).

(* The infimum of the set a above b.                                            *)
Definition infAbove (b a:U) : U := inf (a :\: b).

(* Notation "inf(>: b ) a" := (infAbove b a)                                    *)
Global Instance SetInfAbove : InfAbove U := { infAbove := infAbove }.

Proposition Charac : forall (a x y:U),
  x :< inf a  ->
  y :< a      ->
  Ordinal y   ->
  x :< y.
Proof.
  intros a x y H1 H2 H3. apply Inter.Charac with :{a | Ordinal}:.
  1: assumption. apply Specify.Charac. split; assumption.
Qed.

Proposition CharacRev : forall (a x:U),
  :{a | Ordinal}:  <> :0:                   ->
  (forall y, y :< a -> Ordinal y -> x :< y) ->
  x :< inf a.
Proof.
  intros a x H1 H2. apply Inter.CharacRev. 1: assumption.
  intros y H3. apply Specify.Charac in H3. destruct H3 as [H3 H4].
  apply H2; assumption.
Qed.

Proposition CharacAbove : forall (a b x y:U),
  x :< inf(>: b) a  ->
  y :< a            ->
  ~ y :< b          ->
  Ordinal y         ->
  x :< y.
Proof.
  intros a b x y H1 H2 H3 H4. apply Charac with (a :\: b); try assumption.
  apply Diff.Charac. split; assumption.
Qed.

Proposition CharacAboveRev : forall (a b x:U),
  :{ a :\: b | Ordinal }:  <> :0:                      ->
  (forall y, y :< a -> ~ y :< b -> Ordinal y -> x :< y) ->
  x :< inf(>: b) a.
Proof.
  intros a b x H1 H2. apply Inter.CharacRev. 1: assumption.
  intros y H3. apply Specify.Charac in H3. destruct H3 as [H3 H4].
  apply Diff.Charac in H3. destruct H3 as [H3 H5]. apply H2; assumption.
Qed.

(* The infimum of the class is the class of the infimum.                        *)
Proposition ToClass : forall (a:U),
  Class.Ordinal.Inf.inf (toClass a) :~: toClass (inf a).
Proof.
  intros a x. split; intros H1.
  - apply FromClass.Charac.
    apply Class.Inter.EquivCompat' with (toClass a :/\: On). 2: assumption.
    intros y. split; intros H2.
    + apply Specify.Charac in H2. destruct H2 as [H2 H3]. split; assumption.
    + destruct H2 as [H2 H3]. apply Specify.Charac. split; assumption.
  - apply FromClass.Charac in H1.
    apply Class.Inter.EquivCompat' with (toClass :{a|Ordinal}:). 2: assumption.
    intros y. split; intros H2.
    + destruct H2 as [H2 H3]. apply Specify.Charac. split; assumption.
    + apply Specify.Charac in H2. destruct H2 as [H2 H3]. split; assumption.
Qed.

(* The infimum above b of the class is the class of the infimum above b.        *)
Proposition ToClassAbove : forall (a b:U),
  inf(>: b) (toClass a) :~: toClass (inf(>: b) a).
Proof.
  intros a b. apply EquivTran with (Class.Ordinal.Inf.inf (toClass (a :\: b))).
  - apply Inf.EquivCompat, EquivSym, Diff.ToClass.
  - apply ToClass.
Qed.

(* The infimum of an ordinal is simply its intersection.                        *)
Proposition WhenOrdinal : forall (a:U),
  Ordinal a -> inf a = :I(a).
Proof.
  intros a H1. unfold inf.
  assert (:{a | Ordinal}: = a) as H2. {
    apply Specify.IsA. intros x H2. apply Core.IsOrdinal with a; assumption. }
  rewrite H2. reflexivity.
Qed.

(* When ordinals, the infimum of a above b is the intersection of a\b.          *)
Proposition WhenOrdinalAbove : forall (a b:U), Ordinal a -> Ordinal b ->
  inf(>: b) a = :I(a :\: b).
Proof.
  intros a b H1 H2. unfold Notation.InfAbove.infAbove, infAbove, SetInfAbove.
  unfold infAbove, inf.
  assert (:{a :\: b | Ordinal}: = a :\: b) as H3. {
    apply Specify.IsA. intros x H3. apply Core.IsOrdinal with a.
    1: assumption. apply Diff.Charac in H3. apply H3. }
  rewrite H3. reflexivity.
Qed.

(*
(* The supremum of an ordinal is an ordinal.                                    *)
Proposition IsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (sup a).
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsOrdinal. assumption.
Qed.

(* The supremum of the successor of an ordinal is the ordinal.                  *)
Proposition WhenSucc : forall (a:U), Ordinal a ->
  sup (succ a) = a.
Proof.
  intros a H1. rewrite WhenOrdinal.
  - apply UnionOfSucc. assumption.
  - apply Succ.IsOrdinal. assumption.
Qed.

(* The supremum of a limit ordinal is itself.                                   *)
Proposition WhenLimit : forall (a:U),
  Limit a -> sup a = a.
Proof.
  intros a H1.
  assert (Ordinal a) as H2. { apply Limit.HasOrdinalElem. assumption. }
  rewrite WhenOrdinal. 2: assumption. symmetry. apply Limit.Charac in H1.
  2: assumption. destruct H1 as [_ H1]. assumption.
Qed.

(* The supremum of N is N itself.                                               *)
Proposition WhenOmega : sup :N = :N.
Proof.
  apply WhenLimit. apply Omega.IsLimit.
Qed.

(* A non-empty, non-limit ordinal is equal to the successor of its supremum.    *)
Proposition WhenNonLimit : forall (a:U),
  NonLimit a -> a <> :0: -> a = succ (sup a).
Proof.
  intros a H1 H2.
  assert (Ordinal a) as H3. { apply NonLimit.HasOrdinalElem. assumption. }
  rewrite WhenOrdinal. 2: assumption.
  apply NonLimit.Charac in H1. 2: assumption.
  destruct H1 as [H1|H1]. 2: assumption. contradiction.
Qed.

(* If b belongs to a, the supremum of a below succ b is b.                      *)
Proposition WhenElem : forall (a b:U), Ordinal a -> Ordinal b ->
  b :< a -> sup(:< succ b) a = b.
Proof.
  intros a b H1 H2 H3.
  assert (a :/\: succ b = succ b) as H4. {
    apply ElemIsIncl in H3; try assumption.
    apply ZF.Set.Incl.DoubleInclusion. split; intros x H4.
    - apply Inter2.Charac in H4. destruct H4 as [_ H4]. assumption.
    - apply Inter2.Charac. split. 2: assumption. apply H3. assumption. }
  rewrite WhenOrdinalBelow. 2: assumption.
  - rewrite H4. apply UnionOfSucc. assumption.
  - apply Succ.IsOrdinal. assumption.
Qed.

(* The supremum of an ordinal is an upper-bound of its elements.                *)
Proposition IsUpperBound : forall (a b:U), Ordinal a ->
  b :< a -> b :<=: sup a.
Proof.
  intros a b H1 H2. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsUpperBound; assumption.
Qed.

(* The supremum of an ordinal is the smallest upper-bound.                      *)
Proposition IsSmallest : forall (a b:U),
  Ordinal a                       ->
  Ordinal b                       ->
  (forall c, c :< a -> c :<=: b)  ->
  sup a :<=: b.
Proof.
  intros a b H1 H2. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsSmallest; assumption.
Qed.

(* The supremum of an ordinal is not an element of it iff it is equal to it.    *)
Proposition NotElemIsEqual : forall (a:U), Ordinal a ->
  ~ sup a :< a <-> sup a = a.
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.NotElemIsEqual. assumption.
Qed.

(* The supremum of an ordinal is a subset of it.                                *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  sup a :<=: a.
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsIncl. assumption.
Qed.
*)
