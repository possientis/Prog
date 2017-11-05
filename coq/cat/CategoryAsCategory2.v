Require Import Category2.
Require Import Category.
Require Import Category2AsCategory.



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

Lemma Obj_inversion : forall (A:Type) (c: Category A) (x y:A)
(px : source c x = x) (py: source c y= y),
    obj x px = obj y py -> x = y.
Proof.
    intros A c x y px py H.
    assert (x = mor (obj x px)) as Hx. { reflexivity. }
    assert (y = mor (obj y py)) as Hy. { reflexivity. }
    rewrite Hx, Hy, H. reflexivity.
Qed.


(* cheating ... can't get proof irrelevance to work *)
Axiom Axiom_Obj_equal : forall (A:Type) (c: Category A) (x y: Obj c),
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
Proof. intros a. destruct a. apply Axiom_Obj_equal. simpl. exact e. Qed.

Definition proof_tid_ (A:Type) (c:Category A) : forall a:Obj c, 
    cod_ c (id_ c a) = a.
Proof.
    intros a. destruct a as [a p].
    apply Axiom_Obj_equal. simpl.
    assert (target c (source c a) = target c a) as H . { rewrite p. reflexivity. }
    rewrite (proof_ts c a) in H. rewrite <- H. exact p.
Qed.

Definition proof_dom2_ (A:Type) (c:Category A) : forall f g: A,
    cod_ c f = dom_ c g <-> compose2_ c f g <> None.
Proof.
    intros f g. split. 
    - intros H. apply (proof_dom c). apply Obj_inversion in H. exact H.
    - intros H. apply Axiom_Obj_equal. simpl. apply (proof_dom c). exact H.
Qed.

Definition proof_src2_ (A:Type) (c:Category A) : forall f g h: A,
    compose2_ c f g = Some h -> dom_ c h = dom_ c f.
Proof.
    intros f g h H.
    apply Axiom_Obj_equal. apply (proof_src c) with (g:=g). exact H.
Qed.

Definition proof_tgt2_ (A:Type) (c:Category A) : forall f g h: A,
    compose2_ c f g = Some h -> cod_ c h = cod_ c g.
Proof.
    intros f g h H.
    apply Axiom_Obj_equal. apply (proof_tgt c) with (f:=f). exact H.
Qed.

Definition proof_idl2_ (A:Type) (c:Category A) : forall (a:Obj c) (f:A),
    a = dom_ c f -> compose2_ c (id_ c a) f = Some f.
Proof.
    intros a f H. apply (proof_idl c). 
    destruct a as [a p]. apply Obj_inversion in H. exact H.
Qed.

Definition proof_idr2_ (A:Type) (c:Category A) : forall (a:Obj c) (f:A),
    a = cod_ c f -> compose2_ c f (id_ c a) = Some f.
Proof.
    intros a f H. apply (proof_idr c). 
    destruct a as [a p]. apply Obj_inversion in H. exact H.
Qed.

Definition proof_asc2_ (A:Type) (c:Category A) : forall f g h fg gh:A,
    compose2_ c f g = Some fg ->
    compose2_ c g h = Some gh ->
    compose2_ c f gh = compose2_ c fg h.
Proof.
    intros f g h fg gh H1 H2. apply (proof_asc c) with (g:=g).
    exact H1. exact H2.
Qed.


Definition toCategory2 (A:Type) (c:Category A) : Category2 (Obj c) A := category2
    (dom_               c)
    (cod_               c)
    (compose2_          c)
    (id_                c)
    (proof_sid_     A   c)
    (proof_tid_     A   c)
    (proof_dom2_    A   c)
    (proof_src2_    A   c)
    (proof_tgt2_    A   c)
    (proof_idl2_    A   c)
    (proof_idr2_    A   c)
    (proof_asc2_    A   c). 

Arguments toCategory2 {A} _.

Theorem CatCat : forall (A:Type) (c:Category A),
    toCategory (toCategory2 c) = c.
Proof.
    intros A c. apply Axiom_Category_equal.
    - intros f. reflexivity.
    - intros f. reflexivity.
    - intros f g. reflexivity.
Qed.





