Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Total.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Image.


Module COM := Class.Order.Minimal.

(* Predicate expressing the fact that b is an r-minimal element of a.           *)
Definition Minimal (r a b:U) : Prop
  := b :< a /\ (forall x, x :< a  -> ~ :(x,b): :< r).

(* If b is minimal w.r. to the sets, then it is minimal w.r. to the classes.    *)
Proposition ToClass : forall (r a b:U),
  Minimal r a b -> COM.Minimal (toClass r) (toClass a) b.
Proof.
  intros r a b H1. assumption.
Qed.

(* If b is minimal w.r. to the classes, then it is minimal w.r. to the sets.    *)
Proposition FromClass : forall (r a b:U),
  COM.Minimal (toClass r) (toClass a) b -> Minimal r a b.
Proof.
  intros r a b H1. assumption.
Qed.

(* A minimal element of a belongs to a.                                         *)
Proposition IsIn : forall (r a b:U),
  Minimal r a b -> b :< a.
Proof.
  intros r a b H1. apply H1.
Qed.

(* If r is total, a minimal element of b is below every element of b.           *)
Proposition WhenIn : forall (r a b x y:U),
  Total r a                 ->
  b :<=: a                  ->
  Minimal r b x             ->
  y :< b                    ->
  x = y \/ :(x,y): :< r.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros r a b x y H1 H2 H3 H4.
  (* Since x and y are both elements of a, totality compares them.              *)
  assert (x = y \/ :(x,y): :< r \/ :(y,x): :< r) as H5. {
    apply H1; apply H2. 2: assumption. apply IsIn with r. assumption. }
  (* Equality and x below y give the desired conclusion; y below x contradicts  *)
  (* minimality of x inside b.                                                  *)
  destruct H5 as [H5|[H5|H5]].
  - left. assumption.
  - right. assumption.
  - exfalso. revert H5. apply H3. assumption.
Qed.

(* An isomorphism sends a minimal element to a minimal image element.           *)
Proposition IsomImage : forall (f r s a b c x:U),
  Isom f r s a b          ->
  c :<=: a                ->
  x :< a                  ->
  Minimal r c x           ->
  Minimal s f:[c]: f!x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f r s a b c x H1 H2 H3 [H4 H5]. split.
  - (* The image point lies in the image of c because x lies in c.              *)
    apply (Bij.ImageCharac f a b c). 1: apply H1.
    exists x. split. 1: assumption. split. 1: assumption. reflexivity.
  - (* Any image predecessor below f!x pulls back to a predecessor below x.     *)
    intros y H6 H7. apply (Bij.ImageCharac f a b c) in H6. 2: apply H1.
    destruct H6 as [z [H6 [H8 H9]]]. rewrite <- H9 in H7.
    apply H1 in H7; try assumption. specialize (H5 z H6). contradiction.
Qed.

(* If r is total on a then the minimal element of a subset of a is unique.      *)
Proposition IsUnique : forall (r a b x y:U),
  Total r a       ->
  b :<=: a        ->
  Minimal r b x   ->
  Minimal r b y   ->
  x = y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros r a b x y H1 H2 H3 H4.
  (* The first minimal element is either equal to the second or below it.       *)
  assert (x = y \/ :(x,y): :< r) as H5. {
    apply WhenIn with a b; try assumption. apply IsIn with r. assumption. }
  (* The below case contradicts the minimality of the second element.           *)
  destruct H5 as [H5|H5]. 1: assumption. exfalso.
  assert (~ :(x,y): :< r) as H6. { apply H4. apply IsIn with r. assumption. }
  contradiction.
Qed.
