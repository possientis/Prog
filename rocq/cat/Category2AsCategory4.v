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


Definition proof_sid4_ (Obj Mor:Type) (c:Category2 Obj Mor):forall (a: Obj4_ c),
    dom4_ c (id4_ c a) = a.
Proof. apply (proof_sid c). Qed.

Definition proof_tid4_(Obj Mor:Type)(c:Category2 Obj Mor):forall (a: Obj4_ c),
    cod4_ c (id4_ c a) = a.
Proof. apply (proof_tid c). Qed.

Definition proof_dom4_(Obj Mor:Type)(c:Category2 Obj Mor):forall (f g: Mor4_ c),
    cod4_ c f = dom4_ c g <-> compose4_ c f g <> None.
Proof. apply (proof_dom2 c). Qed. 

Definition proof_src4_(Obj Mor:Type)(c:Category2 Obj Mor):forall (f g h: Mor4_ c),
    compose4_ c f g = Some h -> dom4_ c h = dom4_ c f.
Proof. apply (proof_src2 c). Qed.

Definition proof_tgt4_(Obj Mor:Type)(c:Category2 Obj Mor):forall (f g h: Mor4_ c),
    compose4_ c f g = Some h -> cod4_ c h = cod4_ c g.
Proof. apply (proof_tgt2 c). Qed.

Definition proof_idl4_(Obj Mor:Type)(c:Category2 Obj Mor):forall (a:Obj4_ c),
    forall (f:Mor4_ c), a = dom4_ c f -> compose4_ c (id4_ c a) f = Some f.
Proof. apply (proof_idl2 c). Qed.

Definition proof_idr4_(Obj Mor:Type)(c:Category2 Obj Mor):forall (a:Obj4_ c),
    forall (f:Mor4_ c), a = cod4_ c f -> compose4_ c f (id4_ c a) = Some f.
Proof. apply (proof_idr2 c). Qed.

Definition proof_asc4_(Obj Mor:Type)(c:Category2 Obj Mor):
    forall (f g h fg gh:Mor4_ c), compose4_ c f g = Some fg ->
    compose4_ c g h = Some gh -> compose4_ c f gh = compose4_ c fg h.
Proof. apply (proof_asc2 c). Qed.

Definition toCategory4(Obj Mor:Type)(c:Category2 Obj Mor):Category4 := category4
    (Obj4_                  c)
    (Mor4_                  c)
    (dom4_                  c)
    (cod4_                  c)
    (compose4_              c)
    (id4_                   c)
    (proof_sid4_ Obj Mor    c)
    (proof_tid4_ Obj Mor    c)
    (proof_dom4_ Obj Mor    c)
    (proof_src4_ Obj Mor    c)
    (proof_tgt4_ Obj Mor    c)
    (proof_idl4_ Obj Mor    c)
    (proof_idr4_ Obj Mor    c)
    (proof_asc4_ Obj Mor    c).

Arguments toCategory4 {Obj} {Mor} _.





