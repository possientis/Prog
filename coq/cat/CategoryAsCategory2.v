Require Import Category2.
Require Import Category.



(* given a category we define the data necessary to create a category2 *)

Inductive Obj (A:Type) (c: Category A) : Type := 
    obj : forall a:A, source c a = a -> Obj A c.

Arguments Obj {A} _.
Arguments obj {A} {c}.

Definition mor (A:Type) (c: Category A) (x: Obj c) : A :=
    match x with
    | obj a _     => a
    end.

Arguments mor {A} {c} _.

(* cheating ... can't get proof irrelevance to work *)
Axiom obj_equal : forall (A:Type) (c: Category A) (x y: Obj c),
    mor x = mor y -> x = y.



Definition toObject (A:Type) (c:Category A) (a:A) : source c a = a -> Obj c := 
    obj a. 

Arguments toObject {A} {c} {a} _.


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
    | obj f _   => f
    end.

Arguments dom_ {A} _ _.
Arguments cod_ {A} _ _.
Arguments compose2_ {A} _ _ _.
Arguments id_ {A} _ _.

Definition proof_sid_ (A:Type) (c:Category A) : forall a:Obj c, 
    dom_ c (id_ c a) = a.
Proof.
    intros a. destruct a. simpl. unfold dom_. unfold toObject.
    apply obj_equal. simpl. exact e.
Qed.

Definition proof_tid_ (A:Type) (c:Category A) : forall a:Obj c, 
    cod_ c (id_ c a) = a.
Proof.
    intros a. destruct a as [a p].
    simpl. unfold cod_. unfold toObject.
    apply obj_equal. simpl.
    assert (target c (source c a) = target c a) as H . { rewrite p. reflexivity. }
    rewrite (proof_ts c a) in H. rewrite <- H. exact p.
Qed.

Definition proof_dom2_ (A:Type) (c:Category A) : forall f g: A,
    cod_ c f = dom_ c g <-> compose2_ c f g <> None.
Proof.


Show.








