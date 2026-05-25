Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.

Module SOC := ZF.Set.Ordinal.Core.
Module SFI := ZF.Set.Relation.Fun.IfThenElse.
Module SRO := ZF.Set.Relation.Onto.
Module SRR := ZF.Set.Relation.Range.

(* A non-empty included ordinal is the range of an ordinal retraction.          *)
Proposition WhenIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  b <> :0: -> b :<=: a -> exists f, SRO.Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3 H4.
  (* Map elements of b to themselves and all remaining elements of a to 0.      *)
  remember (SFI.ifThenElse a (fun x => x :< b) (fun x => x) (fun _ => :0:))
    as f eqn:H5.
  exists f. rewrite H5. split. 1: apply SFI.IsFunctionOn.
  apply Incl.Double. split.
  - intros y H6. apply SRR.Charac in H6. destruct H6 as [x H6].
    apply SFI.Charac2 in H6. destruct H6 as [[H6 [_ H7]]|[H6 [_ _]]].
    + rewrite H6. assumption.
    + rewrite H6. apply SOC.HasZero; assumption.
  - intros y H6. apply SRR.Charac. exists y.
    apply (SFI.Satisfies1 (fun x => x :< b) (fun x => x) (fun _ => :0:) a y).
    + apply H4. assumption.
    + assumption.
Qed.
