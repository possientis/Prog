Parameter set:Type.
Parameter belong: set -> set -> Prop.

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

Axiom set_ext : forall a b:set, 
  subset a b -> subset b a -> a = b.

Definition set_induction_axiom : Prop := forall P:set->Prop,
  (forall X:set, (forall x, belong x X -> P x) -> P X) -> forall X:set, P X.

Definition empty(a:set): Prop := forall x:set, ~ belong x a.

Definition regularity_axiom : Prop := forall a:set, ~ empty a -> 
  exists b, belong b a /\ ~ (exists c:set, belong c a /\ belong c b). 

Proposition induction_imp_regularity: 
  set_induction_axiom -> regularity_axiom.
Proof.
  intro H. unfold regularity_axiom. intros a Ha.

Show.


