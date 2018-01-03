Require Import Category2.
Require Import Category4.

(* given a Category2 we define the data necessary to create a Category 4 *)

Definition Obj4_ (Obj Mor:Type) (c:Category2 Obj Mor) : Type := Obj.
Definition Mor4_ (Obj Mor:Type) (c:Category2 Obj Mor) : Type := Mor.

Arguments Obj4_ {Obj} {Mor} _.
Arguments Mor4_ {Obj} {Mor} _.

Definition dom4_(Obj Mor:Type)(c:Category2 Obj Mor)(f: Mor4_ c):Obj4_ c := dom c f.
Definition cod4_(Obj Mor:Type)(c:Category2 Obj Mor)(f: Mor4_ c):Obj4_ c := cod c f.

Definition compose4_(Obj Mor:Type)(c:Category2 Obj Mor)(f g: Mor4_ c) : 
    option (Mor4_ c) := compose2 c f g.

Definition id4_(Obj Mor:Type)(c:Category2 Obj Mor)(a: Obj4_ c) : Mor4_ c := id c a.

Arguments dom4_ {Obj} {Mor} _ _.
Arguments cod4_ {Obj} {Mor} _ _.
Arguments compose4_ {Obj} {Mor} _ _ _.
Arguments id4_ {Obj} {Mor} _ _.


Definition proof_sid4_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall (a: Obj4_ c),
    dom4_ c (id4_ c a) = a.
Proof. apply (proof_sid c). Qed.

Definition proof_tid4_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall (a: Obj4_ c),
    cod4_ c (id4_ c a) = a.
Proof. apply (proof_tid c). Qed.

Definition proof_dom4_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall (f g: Mor4_ c),
    cod4_ c f = dom4_ c g <-> compose4_ c f g <> None.
Proof. apply (proof_dom2 c). Qed. 

(* TODO *)


