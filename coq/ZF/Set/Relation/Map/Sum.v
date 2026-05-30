Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Single.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union2.

Module SFI := ZF.Set.Relation.Fun.IfThenElse.
Module SSU := ZF.Set.Sum.

(* The either map applies f on the left summand and g on the right.             *)
Definition either (a b f g:U) : U :=
  ifThenElse (a :++: b) (toClass (:{ :0: }: :x: a))
    (fun z => f!((outR :{ :0: }: a)!z))
    (fun z => g!((outR :{ :1: }: b)!z)).

(* The either map sends a pair of maps to their either.                         *)
Definition eitherMap (a b c:U) : U :=
  from2 (map a c) (map b c) (fun f g => either a b f g).

(* The either of maps a -> c and b -> c is a map a ++ b -> c.                   *)
Proposition IsFun : forall (a b c f g:U),
  Fun f a c -> Fun g b c -> Fun (either a b f g) (a :++: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2. split.
  - unfold either. apply SFI.IsFunctionOn.
  - intros y H3. apply Range.Charac in H3. destruct H3 as [z H3].
    unfold either in H3. apply SFI.Charac2 in H3.
    destruct H3 as [[H3 [H4 H5]]|[H3 [H4 H5]]].
    + rewrite H3. apply Fun.IsInRange with a. 1: assumption.
      apply Fun.IsInRange with (:{ :0: }: :x: a). 2: assumption.
      apply Prod.IsFunR.
    + rewrite H3. apply Fun.IsInRange with b. 1: assumption.
      apply Fun.IsInRange with (:{ :1: }: :x: b). 1: apply Prod.IsFunR.
      unfold sum in H4. apply Union2.Charac in H4.
      destruct H4 as [H4|H4]. 2: assumption. contradiction.
Qed.

(* Evaluating either on the left summand gives the left value.                  *)
Proposition EvalL : forall (a b c f g x:U),
  Fun f a c                           ->
  Fun g b c                           ->
  x :< a                              ->
  (either a b f g)!(:(:0:,x):) = f!x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g x H1 H2 H3. unfold either. rewrite SFI.Eval1.
  - rewrite Prod.EvalR. 1: reflexivity. 2: assumption.
    apply Single.IsIn.
  - unfold sum. apply Union2.Charac. left.
    apply Prod.Charac2. split. 2: assumption.
    apply Single.IsIn.
  - apply Prod.Charac2. split. 2: assumption.
    apply Single.IsIn.
Qed.

(* Evaluating either on the right summand gives the right value.                *)
Proposition EvalR : forall (a b c f g y:U),
  Fun f a c                           ->
  Fun g b c                           ->
  y :< b                              ->
  (either a b f g)!(:(:1:,y):) = g!y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g y H1 H2 H3. unfold either. rewrite SFI.Eval2.
  - rewrite Prod.EvalR. 1: reflexivity. 2: assumption.
    apply Single.IsIn.
  - unfold sum. apply Union2.Charac. right.
    apply Prod.Charac2. split. 2: assumption.
    apply Single.IsIn.
  - intros H4. apply Prod.Charac2 in H4. destruct H4 as [H4 H5].
    apply Single.Charac in H4. symmetry in H4.
    apply ZeroIsNotOne. assumption.
Qed.

(* The either of two identities maps the sum onto the union.                    *)
Proposition Union : forall (a b:U),
  Onto (either a b (id a) (id b)) (a :++: b) (a :\/: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b.
  assert (Fun (id a) a (a :\/: b)) as H1. {
    apply Fun.InclCompatR with a.
    - apply Union2.IsInclL.
    - apply Id.IsFun. }
  assert (Fun (id b) b (a :\/: b)) as H2. {
    apply Fun.InclCompatR with b.
    - apply Union2.IsInclR.
    - apply Id.IsFun. }
  assert (Fun (either a b (id a) (id b)) (a :++: b) (a :\/: b)) as H3. {
    apply IsFun; assumption. }
  assert (range (either a b (id a) (id b)) = a :\/: b) as H4. {
    apply Incl.Double. split.
    - apply H3.
    - intros y H5. apply Union2.Charac in H5. destruct H5 as [H5|H5].
      + apply Fun.RangeCharac with (a :++: b) (a :\/: b). 1: assumption.
        exists (:(:0:,y):). split.
        * unfold sum. apply Union2.Charac. left.
          apply Prod.Charac2. split. 2: assumption. apply Single.IsIn.
        * rewrite (EvalL a b (a :\/: b)); try assumption.
          apply Id.Eval. assumption.
      + apply Fun.RangeCharac with (a :++: b) (a :\/: b). 1: assumption.
        exists (:(:1:,y):). split.
        * unfold sum. apply Union2.Charac. right.
          apply Prod.Charac2. split. 2: assumption. apply Single.IsIn.
        * rewrite (EvalR a b (a :\/: b)); try assumption.
          apply Id.Eval. assumption. }
  split. 1: apply H3. assumption.
Qed.

(* Composing either with the left injection gives the left component.           *)
Proposition ComposeL : forall (a b c f g:U),
  Fun f a c                           ->
  Fun g b c                           ->
  (either a b f g) :.: (inL a b) = f.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2. apply Fun.Equal with a c a c.
  2: assumption. 2: reflexivity.
  - apply Fun.Compose with (a :++: b).
    + apply Sum.IsFunL.
    + apply IsFun; assumption.
  - intros x H3.
    rewrite (Fun.ComposeEval (inL a b) (either a b f g) a (a :++: b) c x).
    4: assumption.
    + rewrite SSU.EvalL, (EvalL a b c); try assumption. reflexivity.
    + apply Sum.IsFunL.
    + apply IsFun; assumption.
Qed.


(* Composing either with the right injection gives the right component.         *)
Proposition ComposeR : forall (a b c f g:U),
  Fun f a c                           ->
  Fun g b c                           ->
  (either a b f g) :.: (inR a b) = g.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f g H1 H2. apply Fun.Equal with b c b c.
  2: assumption. 2: reflexivity.
  - apply Fun.Compose with (a :++: b).
    + apply Sum.IsFunR.
    + apply IsFun; assumption.
  - intros y H3.
    rewrite (Fun.ComposeEval (inR a b) (either a b f g) b (a :++: b) c y).
    4: assumption.
    + rewrite SSU.EvalR, (EvalR a b c); try assumption. reflexivity.
    + apply Sum.IsFunR.
    + apply IsFun; assumption.
Qed.

(* The either map is a map from map(a,c) x map(b,c) to map(a ++ b,c).           *)
Proposition IsFunMap : forall (a b c:U),
  Fun (eitherMap a b c) ((map a c) :x: (map b c)) (map (a :++: b) c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. unfold eitherMap. apply From2.IsFun.
  intros f g H1 H2. apply CharacMap. apply IsFun.
  - apply CharacMap. assumption.
  - apply CharacMap. assumption.
Qed.

