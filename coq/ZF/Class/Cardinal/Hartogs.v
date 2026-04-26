Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Order.E.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Order.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Inj.

Module CRR := ZF.Class.Relation.Relation.
Module SOO := ZF.Set.Ordinal.Order.
Module SRR := ZF.Set.Relation.Relation.

Definition hartogs (a:U) : Class := fun b =>
  Ordinal b /\ exists f, Inj f b a.

Definition isom : Class := fun y => exists r x f, y = :(:(r,x):,f):   /\
  ((~WellOrdering r x /\ f = :0:)                                     \/
   ( WellOrdering r x /\ exists b, Ordinal b /\ Isom f r (E b) x b)).

Proposition Charac2 : forall (r x f:U),
  isom :(:(r,x):,f): <->
  (~WellOrdering r x /\ f = :0:)                                     \/
  ( WellOrdering r x /\ exists b, Ordinal b /\ Isom f r (E b) x b).
Proof.
  (* Proof by Claude.                                                           *)
  (* Direct unfolding of isom: membership reduces to the two-case disjunction.  *)
  (* OrdPair injectivity forces r'=r, x'=x, f'=f, collapsing the existentials.  *)
  intros r x f. unfold isom. split.
  - intros [r' [x' [f' [H1 H2]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4].
    subst. assumption.
  - intros H1. exists r, x, f. split. reflexivity. assumption.
Qed.

(* Every element of isom is an ordered pair of the form ((r,x),f).              *)
Proposition IsRelation : CRR.Relation isom.
Proof.
  (* Proof by Claude.                                                           *)
  (* Any y in isom satisfies y = ((r,x),f) for some r, x, f by definition.      *)
  intros y H. unfold isom in H. destruct H as [r [x [f [H1 _]]]].
  exists :(r,x):. exists f. exact H1.
Qed.

(* isom is functional: each input pair (r,x) determines at most one output.     *)
Proposition IsFunctional : Functional isom.
Proof.
  (* Proof by Claude.                                                           *)
  (* Suppose isom(p,y) and isom(p,z). Both unpack as p = ((r,x),f) for some f;  *)
  intros p y z H1 H2.
  unfold isom in H1. destruct H1 as [r1 [x1 [f1 [Heq1 Hcase1]]]].
  unfold isom in H2. destruct H2 as [r2 [x2 [f2 [Heq2 Hcase2]]]].
  (* pair injectivity forces r and x to agree, reducing to showing f1 = f2.     *)
  apply OrdPair.WhenEqual in Heq1. destruct Heq1 as [Hp1 Hy].
  apply OrdPair.WhenEqual in Heq2. destruct Heq2 as [Hp2 Hz].
  subst y z. rewrite Hp1 in Hp2.
  apply OrdPair.WhenEqual in Hp2. destruct Hp2 as [Hr Hx].
  subst r2 x2.
  (* Split on whether (r,x) is well-ordered: if not, f1 = f2 = 0.               *)
  destruct Hcase1 as [[Hnwo1 Hf1]|[Hwo1 [b1 [Hb1 HIsom1]]]];
  destruct Hcase2 as [[Hnwo2 Hf2]|[Hwo2 [b2 [Hb2 HIsom2]]]].
  - subst. reflexivity.
  - contradiction.
  - contradiction.
  - assert (SRR.Relation f1) as HRf1. { apply HIsom1. }
    assert (SRR.Relation f2) as HRf2. { apply HIsom2. }
    (* Invert: f1^{-1}: b1 -> x and f2^{-1}: b2 -> x are isomorphisms.          *)
    apply Isom.Converse in HIsom1. apply Isom.Converse in HIsom2.
    (* Ordinal order-type uniqueness gives f1^{-1} = f2^{-1}.                   *)
    assert (b1 = b2 /\ f1^:-1: = f2^:-1:) as [_ Hinv]. {
      eapply SOO.IsUnique; eassumption. }
    (* Since f1 and f2 are relations, converse injectivity gives f1 = f2.       *)
    apply Converse.Injective; assumption.
Qed.

(* A well-ordered pair (r,x) with its ordinal isomorphism belongs to isom.      *)
Proposition Satisfies : forall (r x f b:U),
  WellOrdering r x      ->
  Ordinal b             ->
  Isom f r (E b) x b    ->
  isom :(:(r,x):,f):.
Proof.
  (* Proof by Claude.                                                           *)
  (* Unfold the definition: take the well-ordered branch with ordinal b.        *)
  intros r x f b Hwo Hb HIsom.
  unfold isom. exists r, x, f. split. 1: reflexivity.
  right. split. 1: assumption.
  exists b. split; assumption.
Qed.

(* isom is a function: it is both a relation and functional.                    *)
Proposition IsFunction : Function isom.
Proof.
  split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

(* Every ordered pair (r,x) belongs to the domain of isom.                      *)
Proposition DomainOf : forall (r x:U), domain isom :(r,x):.
Proof.
  (* Proof by Claude.                                                           *)
  (* Split on whether r well-orders x; provide a witness f for each case.       *)
  intros r x. unfold domain.
  assert (WellOrdering r x \/ ~ WellOrdering r x) as [Hwo|Hnwo]. {
    apply LawExcludedMiddle. }
  - (* The ordinal order type of (x, r) exists; its converse is the witness.    *)
    assert (exists f a, Ordinal a /\ Isom f (E a) r a x) as [f [a [Ha HIsom]]]. {
      apply SOO.Exists. assumption. }
    apply Isom.Converse in HIsom.
    exists f^:-1:. eapply Satisfies; eassumption.
  - (* Non-WO: the empty set witnesses membership in isom for (r,x).            *)
    exists :0:. unfold isom. exists r, x, :0:. split. 1: reflexivity.
    left. split. 1: assumption. reflexivity.
Qed.

(* Evaluating isom at (r,x) returns f, the ordinal isomorphism for (r,x).       *)
Proposition Eval : forall (r x f b:U),
  WellOrdering r x      ->
  Ordinal b             ->
  Isom f r (E b) x b    ->
  (isom!:(r,x):) = f.
Proof.
  (* Proof by Claude.                                                           *)
  (* The pair ((r,x),f) belongs to isom; convert via the eval characterisation. *)
  intros r x f b Hwo Hb HIsom.
  assert (isom :(:(r,x):,f):) as H. { eapply Satisfies; eassumption. }
  apply (EvalOfClass.Charac isom :(r,x):). 3: assumption.
  - apply IsFunctional.
  - apply DomainOf.
Qed.
