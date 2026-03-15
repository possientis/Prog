Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.TranClosure.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Single.
Require Import ZF.Set.Specify.

Module CEM := ZF.Class.Empty.
Module COT := ZF.Class.Order.TranClosure.

Proposition HasMinimal : forall (R A B:Class),
  WellFounded R A             ->
  B :<=: A                    ->
  B :<>: :0:                  ->
  exists x, Minimal R B x.
Proof.
  intros R A B H1 H2 H3.
  apply CEM.HasElem in H3. destruct H3 as [a H3].
  assert (exists b,
    :{a}: :<=: b                                         /\
    toClass b :<=: A                                      /\
    COT.Transitive R A b                                      /\
    (forall x, x :< b -> exists n g,
      n :< :N                                     /\
      Fun g (succ n) b                            /\
      g!:0: :< :{a}:                              /\
      g!n = x                                     /\
      (forall i, i :< n -> R :(g!(succ i),g!i):))         /\
    (forall c,
      :{a}: :<=: c      ->
      toClass c :<=: A  ->
      Transitive R A c  ->
      b :<=: c)) as H4. {
        apply Exists. 1: assumption. intros x H4.
        apply Single.Charac in H4. subst. apply H2. assumption. }
  destruct H4 as [b [H4 [H5 [H6 _]]]].
  remember {{ x :< b | B }} as c eqn:H7.
  assert (toClass c :<=: A) as H8. {
    intros x H8. rewrite H7 in H8.
    apply Specify.Charac in H8. destruct H8 as [H8 H9].
    apply H2. assumption. }
  assert (c <> :0:) as H9. {
    apply Empty.HasElem. exists a. rewrite H7.
    apply Specify.Charac. split. 2: assumption. apply H4. apply Single.IsIn. }
  assert (exists d, Minimal R (toClass c) d) as H10. { apply H1; assumption. }
  destruct H10 as [d H10].
  assert (toClass c :<=: B) as H11. { rewrite H7. apply Specify.IsInclR. }
  assert (B d) as H12. { apply H11. apply Minimal.IsIn with R. assumption. }
  assert (c :<=: b) as H13. { rewrite H7. apply Specify.IsInclL. }
  assert (d :< b) as H14. {
    apply H13. apply (Minimal.IsIn R (toClass c)). assumption. }
  assert (forall x, B x -> ~ R :( x, d ):) as H15. {
    intros x H15 H16.
    assert (x :< b) as H17. {
      apply H6 with d; try assumption. apply H2. assumption. }
    assert (x :< c) as H18. {
      rewrite H7. apply Specify.Charac. split; assumption. }
    revert H16. apply H10. assumption. }
  exists d. split; assumption.
Qed.
