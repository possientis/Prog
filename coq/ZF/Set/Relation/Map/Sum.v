Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Single.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Union2.
Require Import ZF.Notation.Eval.

Module SFI := ZF.Set.Relation.Fun.IfThenElse.

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
