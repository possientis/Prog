Require Import List.
Set Implicit Arguments.

(* infinite lists *)
CoInductive stream (A:Type): Type :=
  | Cons : A -> stream A -> stream A.

(* finite or infinite lists *)
CoInductive llist (A:Type): Type :=
  | LNil : llist A
  | LCons : A -> llist A -> llist A.

(* finite or infinite binary trees *)
CoInductive ltree (A:Type): Type :=
  | LLeaf : ltree A
  | LBin  : A -> ltree A -> ltree A -> ltree A.


Check (LCons 1 (LCons 2 (LCons 3 (LNil nat)))).

Fixpoint embed {A:Type} (l:list A) : llist A :=
  match l with
    | nil       => LNil A
    | cons a l' => LCons a (embed l')
  end. 

Lemma embed_injective: forall (A:Type)(l m:list A),
  embed l = embed m -> l = m.
Proof.
  intros A l. elim l.
    clear l. intros m. elim m.
      clear m. intros. reflexivity.
      clear m. simpl. intros. discriminate.
    clear l. intros a l IH m. elim m.
      clear m. simpl. intros. discriminate.
      clear m. intros b m H0 H1. clear H0.
        simpl in H1. injection H1. clear H1. intros H1 H2.
        rewrite <- H2. rewrite (IH m). reflexivity. exact H1.
Qed.

(* cannot use a recursive definition with 'Fixpoint' *)
CoFixpoint from (n:nat) : llist nat := LCons n (from (S n)). 

Definition Nats : llist nat := from 0.

Check Nats.

(* 'cofix' for anonymous co-recursive functions *)
Definition Squares_from :=
  let sqr := fun n:nat => n*n in
  cofix F : nat -> llist nat :=
    fun n:nat => LCons (sqr n)(F (S n)).

(* insight : co-recursive -> codomain is a coinductive type
             recursive    -> domain is an inductive type
*)

Eval simpl in (from 3).

Eval compute in (from 3).

CoFixpoint repeat {A:Type}(a:A) : llist A :=  LCons a (repeat a).


CoFixpoint lappend {A:Type}(u v: llist A) : llist A :=
  match u with
    | LNil        => v
    | LCons a u'  => LCons a (lappend u' v)
  end.















