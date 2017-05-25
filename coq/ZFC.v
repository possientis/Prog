Require Import classical.

Axiom LEM : forall p:Prop, ~p \/ p.

Lemma LEM': forall p: Prop, p \/ ~p.
Proof.
  intros p. cut (~p \/ p). intro H. elim H.
  clear H. intro H. right. exact H.
  clear H. intro H. left . exact H.
  apply LEM.
Qed.

Lemma exist_all: forall (A:Type) (P:A->Prop),
  ~(exists x:A, ~P x) -> (forall x:A, P x).
Proof.
  apply imp_or_to_ex_all. apply and_or_to_imp_or. apply lem_to_and_or.
  unfold lem. intro p. apply LEM'.
Qed.


Lemma not_not : forall p:Prop, ~~p <-> p.
Proof.
  intros p. split. apply peirce_to_classic. apply imp_or_to_peirce.
  apply and_or_to_imp_or. apply lem_to_and_or. unfold lem. exact LEM'.
  apply L2.
Qed.


Parameter set:Type.
Parameter belong: set -> set -> Prop.

Definition empty(a:set): Prop := forall x:set, ~ belong x a.

Definition inhabited(a:set) := exists x:set, belong x a.

Proposition empty_not_inhabited : forall a:set,
  inhabited a <-> ~ empty a.
Proof.
  intros a. split. 
  intro Ha. unfold empty. intro Ha'. unfold inhabited in Ha. elim Ha.
  clear Ha. intros x Hxa.  apply (Ha' x). exact Hxa.
  intro Ha. unfold inhabited. unfold empty in Ha.
  cut (~ (exists x:set, belong x a) \/ exists x:set, belong x a).
  intros H. elim H. clear H. intros H. apply False_ind.
  apply Ha. apply exist_all. intros H'. apply H. elim H'.
  clear H'. intros x H'. exists x. apply not_not. exact H'.
  intro H'. exact H'. apply LEM.
Qed.


Definition subset(a b:set) : Prop :=
  forall x:set, belong x a -> belong x b.

Proposition subset_refl : forall a:set, subset a a.
Proof.
  intros a. unfold subset. intros x H. exact H.
Qed.

Proposition subset_trans: forall a b c:set, 
  subset a b -> subset b c -> subset a c.
Proof.
  intros a b c Hab Hbc. unfold subset. intros x Hxa.
  unfold subset in Hab. unfold subset in Hbc.
  apply Hbc. apply Hab. exact Hxa.
Qed.


(* extensionality *)
Axiom set_ext : forall a b:set, 
  subset a b -> subset b a -> a = b.

(* empty set exists *)
Parameter EMPTY : set.
Axiom empty_set : forall x:set, ~belong x EMPTY.

Proposition EMPTY_is_empty : empty(EMPTY).
Proof.
  unfold empty. apply empty_set.
Qed.

Proposition empty_set_unique : forall x:set, empty x -> x = EMPTY.
Proof.
  intros x Hx. unfold empty in Hx. apply set_ext.
  unfold subset. intros y Hyx. apply False_ind. apply (Hx y). exact Hyx.
  unfold subset. intros y Hye. apply False_ind. apply (empty_set y). exact Hye.
Qed.

Proposition empty_iff_EMPTY : forall x:set,
  empty x <-> x = EMPTY.
Proof.
  intros x. split. apply empty_set_unique.
  intros H. rewrite H. exact EMPTY_is_empty.
Qed.

Proposition empty_or_inhabited: forall x:set,
  x = EMPTY \/ inhabited x.
Proof.
  intros x. cut (~ inhabited x \/ inhabited x). intro H. elim H.
  clear H. intro H. left. apply empty_set_unique. apply not_not.
  intro H'. apply H. apply empty_not_inhabited. exact H'.
  clear H. intro H. right. exact H. apply LEM.
Qed.

Parameter UPair : set -> set -> set.
Axiom UPairI1 : forall y z:set, belong y (UPair y z).
Axiom UPairI2 : forall y z:set, belong z (UPair y z).
Axiom UPairE : forall x y z:set, belong x (UPair y z) -> x = y \/ x = z.

Lemma upair_subset: forall a b:set, subset (UPair a b) (UPair b a).
Proof.
  intros a b. unfold subset. intros x Hx. cut (x = a \/ x = b).
  intros H'. elim H'. 
  clear H'. intro H'. rewrite H'. apply UPairI2.
  clear H'. intro H'. rewrite H'. apply UPairI1.
  apply UPairE. exact Hx.
Qed.


Proposition upair_commute : forall a b:set, UPair a b = UPair b a.
Proof.
  intros a b. apply set_ext. apply upair_subset. apply upair_subset. 
Qed.

Parameter Union : set -> set.
Axiom UnionI : forall X x y: set, belong x y -> belong y X -> belong x (Union X).
Axiom UnionE : forall X x: set, 
  belong x (Union X) -> exists y:set, belong x y /\ belong y X.

Parameter Power : set -> set.
Axiom PowerI : forall x y:set, subset y x -> belong y (Power x).
Axiom PowerE : forall x y:set, belong y (Power x) -> subset y x.

Parameter Repl : (set -> set) -> set -> set.
Axiom ReplI : forall (F:set->set)(X:set)(x:set),
  belong x X -> belong (F x) (Repl F X). 
Axiom ReplE : forall (F:set->set)(X:set)(y:set),
  belong y (Repl F X) -> exists x:set, belong x X /\ y = (F x).


(* Grothendieck Universes *)
Parameter GU : set -> set.
Axiom GUI : forall X:set, belong X (GU X).          (* GU X has element X *)

Axiom GUTrans: forall X x y:set,
  belong x y -> belong y (GU X) -> belong x (GU X). (* GU X is transitive set *)

Axiom GUUpair : forall X y x:set,                   (* closure under pairing *)
  belong x (GU X) -> belong y (GU X) -> belong (UPair x y) (GU X).

Axiom GUUnion : forall X x:set,                     (* closure under union *)
  belong x (GU X) -> belong (Union x) (GU X).    

Axiom GUPower : forall X x:set,                     (* closure under power set op *)
  belong x (GU X) -> belong (Power x) (GU X).    

Axiom GURepl : forall (F:set -> set)(X x:set),
  belong x (GU X) -> 
  (forall z:set, belong z x -> belong (F z) (GU X)) ->
  belong (Repl F x) (GU X).






(*

Axiom belong_induction : forall P:set->Prop,
  (forall X:set, (forall x, belong x X -> P x) -> P X) -> forall X:set, P X.

(* TODO
Proposition regularity_axiom : forall a:set, ~ empty a -> 
  exists b, belong b a /\ ~ (exists c:set, belong c a /\ belong c b). 
*)

Proposition not_belong_x_x: forall x:set, ~ belong x x.
Proof.
  apply belong_induction. intros X H. cut (~belong X X \/ belong X X).
  intros L. elim L. clear L. intro L. exact L. clear L. intro L.
  apply H. exact L. apply LEM.
Qed.

*)


