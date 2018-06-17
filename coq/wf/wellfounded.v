(* type of relations on a *)
Definition Relation (a:Type) : Type := a -> a -> Prop.

(* when is a map f:nat -> a a descending chain w.r. to relation r *)
Definition isDescendingChain (a:Type) (r:Relation a) (f:nat -> a) : Prop :=
    forall (n:nat), r (f (S n)) (f n).

Arguments isDescendingChain {a} _ _.

(* a relation on a is well-founded if it has no descending chain *)
Definition isWellFounded (a:Type) (r:Relation a) : Prop :=
    ~(exists (f:nat -> a), isDescendingChain r f).

Lemma induction : forall (a:Type) (r:Relation a) (P:a -> Prop),
(forall x, (forall u, r u x -> P u) -> P x) -> forall x, P x.

Proof.
    intros a r P H.


Show.
