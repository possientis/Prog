Require Import classical.

(************************************************************************)
(*                       The universe of sets                           *)
(************************************************************************)

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


(************************************************************************)
(*                   The law of excluded middle                         *)
(************************************************************************)

Axiom law_excluded_middle : forall p:Prop, ~p \/ p.

Lemma LEM': forall p: Prop, p \/ ~p.
Proof.
  intros p. cut (~p \/ p). intro H. elim H.
  clear H. intro H. right. exact H.
  clear H. intro H. left . exact H.
  apply law_excluded_middle.
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


(************************************************************************)
(*                      The skolemization axiom                         *)
(************************************************************************)

Axiom skolem: forall {A:Type}{P:A->Prop},
  (exists (x:A), P x) ->
  (forall (x y:A), P x -> P y -> x = y) -> { x:A | P x }.


(************************************************************************)
(*                       The extensionality axiom                       *)
(************************************************************************)

Axiom extensionality : forall a b:set, 
  subset a b -> subset b a -> a = b.



(************************************************************************)
(*                      Existence of the empty set                      *)
(************************************************************************)

Definition empty(a:set): Prop := forall x:set, ~ belong x a.

Axiom empty_set_exists : exists x:set, empty x.

Lemma empty_set_is_unique : forall x y:set,
  empty x -> empty y -> x = y.
Proof.
  intros x y Hx Hy. apply extensionality. 
  unfold subset. intros z Hz. unfold empty in Hx. 
  apply False_ind. apply (Hx z). exact Hz.
  unfold subset. intros z Hz. unfold empty in Hy.
  apply False_ind. apply (Hy z). exact Hz.
Qed.

Definition O : set := proj1_sig (skolem empty_set_exists empty_set_is_unique).

Proposition empty_O : empty O.
Proof.
  exact (proj2_sig (skolem empty_set_exists empty_set_is_unique)). 
Qed.

Proposition not_belong_x_O : forall x:set, ~belong x O.
Proof.
  exact empty_O.
Qed.

Proposition empty_x_is_O : forall x:set, empty x -> x = O.
Proof.
  intros x Hx. apply empty_set_is_unique. exact Hx. exact empty_O.
Qed.


Proposition empty_iff_O : forall x:set,
  empty x <-> x = O.
Proof.
  intros x. split. apply empty_x_is_O.
  intros H. rewrite H. exact empty_O.
Qed.

(************************************************************************)
(*                          The pairing axiom                           *)
(************************************************************************)

Axiom pairing : forall a b:set, exists c:set,
  forall x:set, belong x c <-> x = a \/ x = b. 

Definition pair_relation(a b c:set) : Prop :=
  forall x:set, belong x c <-> x = a \/ x = b. 

Lemma pair_is_unique: forall a b:set, forall c d:set,
  pair_relation a b c -> pair_relation a b d -> c = d.
Proof.
  intros a b c d Hc Hd. apply extensionality. 
  unfold subset. intros x Hx. apply Hc in Hx. apply Hd in Hx. exact Hx.
  unfold subset. intros x Hx. apply Hd in Hx. apply Hc in Hx. exact Hx.
Qed.

Definition pair(a b:set) : set := 
  proj1_sig (skolem (pairing a b) (pair_is_unique a b)).


Proposition pair_is_pair : forall a b:set, 
  forall x:set, belong x (pair a b) <-> x = a \/ x = b.
Proof.
  intros a b. exact (proj2_sig (skolem (pairing a b) (pair_is_unique a b))).
Qed.

Lemma UPairI1 : forall a b:set, belong a (pair a b).
Proof.
  intros a b. apply pair_is_pair. left. reflexivity.
Qed.


Lemma UPairI2 : forall a b:set, belong b (pair a b).
Proof.
  intros a b. apply pair_is_pair. right. reflexivity.
Qed.

Lemma UPairE : forall x a b:set, belong x (pair a b) -> x = a \/ x = b.
Proof.
  intros x a b. apply pair_is_pair.
Qed.

Lemma upair_subset: forall a b:set, subset (pair a b) (pair b a).
Proof.
  intros a b. unfold subset. intros x Hx. cut (x = a \/ x = b).
  intros H'. elim H'. 
  clear H'. intro H'. rewrite H'. apply UPairI2.
  clear H'. intro H'. rewrite H'. apply UPairI1.
  apply UPairE. exact Hx.
Qed.

Definition singleton (x:set) : set := pair x x.

Lemma singleton_belong: forall x y:set, belong x (singleton y) <-> x = y.
Proof.
  intros x y. split. intros Hxy. unfold singleton in Hxy.
  apply UPairE in Hxy. elim Hxy.
  clear Hxy. intro Hxy. exact Hxy. clear Hxy. intro Hxy. exact Hxy.
  intros Exy. unfold singleton. rewrite Exy. apply UPairI1.
Qed.


Proposition upair_commute : forall a b:set, pair a b = pair b a.
Proof.
  intros a b. apply extensionality. apply upair_subset. apply upair_subset. 
Qed.

(*

Parameter Union : set -> set.
Axiom UnionI : forall X x y: set, belong x y -> belong y X -> belong x (Union X).
Axiom UnionE : forall X x: set, 
  belong x (Union X) -> exists y:set, belong x y /\ belong y X.

(* axiom of infinity *)
Definition union (a b:set) : set := Union (pair a b).
Definition S (x:set) : set := union x (singleton x).
Definition one : set := S O.
Definition two : set := S one.

Lemma unionl : forall (a b:set), subset a (union a b).
Proof.
  intros a b. unfold subset. intros x Hx. unfold union.
  apply UnionI with (y:= a). exact Hx. apply UPairI1.
Qed.

Lemma unionr : forall (a b:set), subset b (union a b).
Proof.
  intros a b. unfold subset. intros x Hx. unfold union.
  apply UnionI with (y:= b). exact Hx. apply UPairI2.
Qed.

Lemma subset_succ : forall (a:set), subset a (S a).
Proof.
  intros a. unfold S. apply unionl.
Qed.

Lemma belong_succ : forall (a:set), belong a (S a).
Proof.
  intros a. unfold S. unfold union.
  apply UnionI with (y:= singleton a).
  unfold singleton. apply UPairI1. apply UPairI2.
Qed.


Lemma belong_one: forall (a:set),
  belong a one <-> a = O.
Proof.
  intros a. split. intros Ha. unfold one in Ha.
  unfold S in Ha. unfold union in Ha.
  apply UnionE in Ha. elim Ha.
  clear Ha. intros x Hx. elim Hx.
  clear Hx. intros Hx Hx'. apply UPairE in Hx'. elim Hx'.
  clear Hx'. intro Hx'. apply False_ind. apply not_belong_x_O with (x:=a).
  rewrite Hx' in Hx. unfold O in Hx. exact Hx.
  clear Hx'. intro Hx'. rewrite Hx' in Hx. clear Hx'.
  unfold singleton in Hx. apply UPairE in Hx. elim Hx.
  clear Hx. intro Hx. exact Hx.
  clear Hx. intro Hx. exact Hx.
  intro Ha. rewrite Ha. apply belong_succ.
Qed.


Lemma subset_one: forall (a:set), 
  subset a one -> a = O \/ a = one.
Proof.
  intros a Ha. cut (a = O \/ inhabited a). intros H. elim H. 
  clear H. intros H. left. unfold O. exact H.
  clear H. intros H. right.  apply set_ext. exact Ha.
  unfold subset. intros x Hx. apply belong_one in Hx.
  rewrite Hx. clear Hx x. unfold inhabited in H. elim H.
  clear H. intros x Hx. cut (x = O). intros Hx'.
  rewrite Hx' in Hx. exact Hx. apply belong_one. apply Ha. exact Hx.
  apply empty_or_inhabited.
Qed.
  
Parameter N : set.
Axiom NI0 : belong O N.
Axiom NIS : forall x:set, belong x N -> belong (S x) N.
Axiom NMin : forall M:set,
  belong O M -> (forall x:set, belong x M -> belong (S x) M) -> subset N M.


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

Axiom GUUpair : forall X x y:set,                   (* closure under pairing *)
  belong x (GU X) -> belong y (GU X) -> belong (pair x y) (GU X).

Axiom GUUnion : forall X x:set,                     (* closure under union *)
  belong x (GU X) -> belong (Union x) (GU X).    

Axiom GUPower : forall X x:set,                     (* closure under power set op *)
  belong x (GU X) -> belong (Power x) (GU X).    

Axiom GURepl : forall (X:set)(F:set -> set)(x:set),
  belong x (GU X) -> 
  (forall z:set, belong z x -> belong (F z) (GU X)) ->
  belong (Repl F x) (GU X).

Definition transitive (X:set) : Prop :=
  forall (x y:set), belong x y -> belong y X -> belong x X.

Lemma GUTransitive: forall X:set, transitive (GU X).
Proof.
  intros X. unfold transitive. apply GUTrans. 
Qed.

Definition pairClosed (X:set) : Prop :=
  forall (x y :set),  belong x X -> belong y X -> belong (pair x y) X.

Lemma GUPairClosed: forall X:set, pairClosed (GU X).
Proof.
  intros X. unfold pairClosed. apply GUUpair. 
Qed.

Definition unionClosed (X:set) : Prop :=
  forall x:set,  belong x X -> belong (Union x) X.

Lemma GUUnionClosed: forall X:set, unionClosed (GU X).
Proof.
  intros X. unfold unionClosed. apply GUUnion. 
Qed.

Definition powerClosed (X:set) : Prop :=
  forall x:set,  belong x X -> belong (Power x) X.

Lemma GUPowerClosed: forall X:set, powerClosed (GU X).
Proof.
  intros X. unfold powerClosed. apply GUPower. 
Qed.

Definition replClosed (X:set) : Prop :=
  forall (F:set->set)(x:set),
  belong x X -> (forall z:set, belong z x -> belong (F z) X) -> belong (Repl F x) X.

Lemma GUReplClosed: forall X:set, replClosed (GU X).
Proof.
  intros X. unfold replClosed. apply GURepl. 
Qed.

Definition GrothendieckUniverse (X:set) : Prop :=
  transitive  X /\
  pairClosed  X /\
  unionClosed X /\
  powerClosed X /\
  replClosed  X.

Lemma GU_GU: forall X:set, GrothendieckUniverse (GU X).
Proof.
  intros X. unfold GrothendieckUniverse. split.
  apply GUTransitive. split.
  apply GUPairClosed. split.
  apply GUUnionClosed. split.
  apply GUPowerClosed.
  apply GUReplClosed.
Qed.

Axiom GUMin : forall (X U:set),
  GrothendieckUniverse U -> subset (GU X) U.


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
