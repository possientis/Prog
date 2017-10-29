Require Import Category2.
Require Import Category.

(* given a category we define the data necessary to create a category2 *)



(* by providing the proof that source (source f) = source f
   we are able to cast 'source f' as an object              *)
Definition dom_ (A:Type) (c:Category A) (f:A) : Obj c :=
    toObject (proof_ss c f).


(* by providing the proof that source (target f) = target f
   we are able to cast 'target f' as an object              *)
Definition cod_ (A:Type) (c:Category A) (f:A) : Obj c :=
    toObject (proof_st c f).

Definition compose2_ (A:Type) (c:Category A) (f g:A) : option A := compose c f g.


(* An element of Obj c is effectively a triplet consisting of
   a predicate, a value, and a proof that the value satisfies
   the predicate. We simply return the value                  *)
Definition id_ (A:Type) (c:Category A) (a : Obj c) : A :=
    match a with
    | exist _ f _   => f
    end.

Arguments dom_ {A} _ _.
Arguments cod_ {A} _ _.
Arguments compose2_ {A} _ _ _.
Arguments id_ {A} _ _.

Definition proof_sid_ (A:Type) (c:Category A) : forall a:Obj c, 
    dom_ c (id_ c a) = a.
Proof.
    intros a. destruct a. simpl. unfold dom_. unfold toObject.

Show.



