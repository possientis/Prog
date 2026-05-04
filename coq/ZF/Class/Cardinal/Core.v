Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Foundation.


(* The class of cardinal numbers is a proper class.                             *)
Proposition IsProperChoice : Choice -> Proper Cardinal.
Proof.
  intros AC H1. apply Small.IsSomeSet in H1. destruct H1 as [a H1].
  assert (toClass a :<=: Cardinal) as H2. { intros x H2. apply H1. assumption. }
  assert (exists b, Cardinal b /\ forall c, c :< a -> c :< b) as H3. {
    apply LargerCardinal; assumption. }
  destruct H3 as [b [H3 H4]].
  assert (b :< a) as H5. { apply H1. assumption. }
  assert (b :< b) as H6. { apply H4. assumption. }
  revert H6. apply NoElemLoop1.
Qed.

