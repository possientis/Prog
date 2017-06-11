Require Import classical.

Require Import Axiom_LEM.
Require Import set.
Require Import Axiom_Skolem.
Require Import belong.
Require Import Axiom_Empty_Set.
Require Import Axiom_Pairing.
Require Import subset.
Require Import Axiom_Extensionality.
Require Import empty.
Require Import pair.
Require Import singleton.


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



(*

(* axiom of infinity *)

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
