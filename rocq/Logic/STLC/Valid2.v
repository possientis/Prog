(* This module only serves to demonstrate that defining the notion of well-     *)
(* formed type expression without reference to valid contexts is legitimate.    *)
(* More precisely, we define an alternative definition of validity which is     *)
(* coupled with the definition of well-formed type expressions, where those     *)
(* can only occur in a valid context. We show that this new notion of valid     *)
(* context is equivalent to our existing notion (see Theorem below).            *)

Require Import Logic.STLC.Valid.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

(* New notion of validity and new notion of well-formed type expression,        *)
(* defined as mutually recursive predicates. We now require the context         *)
(* involved in a well-formed type expression to be valid.                       *)
(* Note that these definitions cannot be decoupled from one another.            *)
(* Compare with the definiton of Valid.                                         *)
Inductive Valid2 (b v:Type) : Context -> Prop :=
| Valid2O   : Valid2 b v O
| Valid2Ty  : forall (G:Context) (t:b),
    Valid2 b v G -> Valid2 b v (G ; t ::: *)
| Valid2Var : forall (G:Context) (x:v) (Ty:T b),
    Valid2 b v G -> IsType2 b v G Ty -> Valid2 b v (G ; x ::: Ty) 
(* Compare with the definition of IsType.                                       *)
with IsType2 (b v:Type) : @Context b v -> T b -> Prop :=
| TVar2 : forall (G:Context) (t:b),
    Valid2 b v G    ->          (* We require the context to be valid.          *)
    G >> t          ->
    IsType2 b v G 't
| TFun2 : forall (G:Context) (Ty Ty':T b),
    Valid2 b v G        ->      (* We require the context to be valid.          *)
    IsType2 b v G Ty    ->
    IsType2 b v G Ty'   ->
    IsType2 b v G (Ty :-> Ty')
.

Arguments Valid2    {b} {v}.
Arguments Valid2O   {b} {v}.
Arguments Valid2Ty  {b} {v}.
Arguments Valid2Var {b} {v}.
Arguments IsType2   {b} {v}.
Arguments TVar2     {b} {v}.
Arguments TFun2     {b} {v}.

(* The defining requirements for IsType2 appear to be stronger than those of    *)
(* IsType, so we expect the implication IsType2 G Ty -> IsType G Ty to hold.    *)
Lemma IsType2IsType : forall (b v:Type) (G:@Context b v) (Ty:T b),
    IsType2 G Ty -> G :> Ty.
Proof.
   intros b v G Ty H1. induction H1 as [G Ty H2 H3|G Ty Ty' H2 H3 IH1 H4 IH2]. 
   - constructor. assumption.
   - constructor; assumption.
Qed.

(* The defining requirements for Valid2 are based on a stronger IsType2, so we  *)
(* expect the implication Valid2 G -> Valid G to hold.                          *)
Lemma Valid2Valid : forall (b v:Type) (G:@Context b v),
    Valid2 G -> Valid G.
Proof.
    intros b v G H1. induction H1 as [ |G Ty H2 IH|G x Ty H2 IH H3]. 
    - constructor.
    - constructor. assumption.
    - constructor; try assumption. apply IsType2IsType. assumption.
Qed.

(* We cannot expect the implication IsType G Ty -> IsType2 G Ty to hold, but    *)
(* this is however true if the context involved is 'strongly' valid.            *)
Lemma IsTypeIsType2 : forall (b v:Type) (G:@Context b v) (Ty:T b),
    Valid2 G -> G :> Ty -> IsType2 G Ty.
Proof.
    intros b v G Ty H H1. revert H.
    induction H1 as [G t|G Ty Ty' H2 IH1 H3 IH2].
    - intros H4. constructor; assumption.
    - intros H4. constructor.
        + assumption.
        + apply IH1. assumption.
        + apply IH2. assumption.
Qed.

(* This is the main helper lemma: the conclusion of this lemma needs to be      *)
(* strong enough so we are able to carry out the induction argument.            *)
Lemma ValidValid2IsType2 : forall (b v:Type) (G:@Context b v),
    Valid G -> Valid2 G /\ (forall (Ty:T b), G :> Ty -> IsType2 G Ty).
Proof.
    intros b v G H1. induction H1 as [ |G t H2 IH|G x Ty H2 IH H3].
    - split; try constructor. intros Ty H2. 
      apply notIsTypeInO in H2. contradiction.
    - destruct IH as [IH1 IH2]. split.
        + constructor. assumption.
        + intros Ty H3. apply IsTypeIsType2; try assumption.
          constructor. assumption.
    - destruct IH as [IH1 IH2]. split.
        + constructor; try assumption. apply IH2. assumption.
        + intros Ty' H4. apply IsTypeIsType2; try assumption.
          constructor; try assumption. apply IH2. assumption.
Qed.

(* This is a strenghening of the IsTypeIsType2 result, where we can now rely    *)
(* on the weaker assumption that the context is simply valid (not 'strongly').  *)
Lemma IsTypeIsType2' : forall (b v:Type) (G:@Context b v) (Ty:T b),
    Valid G -> G :> Ty -> IsType2 G Ty.
Proof.
    intros b v G Ty H1 H2. apply ValidValid2IsType2 in H1.
    destruct H1 as [H1 H3]. apply H3. assumption.
Qed.

(* So our seemingly weaker notion of validity actually implies strong validity. *)
Lemma ValidValid2 : forall (b v:Type) (G:@Context b v),
    Valid G -> Valid2 G.
Proof.
    intros b v G H1. apply ValidValid2IsType2 in H1.
    destruct H1 as [H1 H2]. assumption.
Qed.

(* This vindicates our approach of decoupling the notions of valid context and  *)
(* well-formed type expressions, where the latter need not require validity.    *)
Theorem ValidValid2Same : forall (b v:Type) (G:@Context b v),
    Valid G <-> Valid2 G.
Proof.
    intros b v G. split; intros H1.
    - apply ValidValid2. assumption.
    - apply Valid2Valid. assumption.
Qed.
