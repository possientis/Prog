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
Parameter EMPTY : set.
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
Axiom empty_set : forall x:set, ~belong x EMPTY.

Proposition EMPTY_empty : empty(EMPTY).
Proof.
  unfold empty. apply empty_set.
Qed.

Proposition empty_set_unique : forall x:set, empty x -> x = EMPTY.
Proof.
  intros x Hx. unfold empty in Hx. apply set_ext.
  unfold subset. intros y Hyx. apply False_ind. apply (Hx y). exact Hyx.
  unfold subset. intros y Hye. apply False_ind. apply (empty_set y). exact Hye.
Qed.

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



