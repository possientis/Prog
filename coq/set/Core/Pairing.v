(* NEXT: ===> Empty                                                             *) 


Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.Extensionality.

(* In this module, we aim at proving the pairing axiom is satisfied in our      *) 
(* model. So we define the 'pair' {x,y} given two sets x and y. For computer    *)
(* scientists, note that this pair {x,y} is a set and should not be confused    *)
(* with the 'tuple' (x,y) commonly known as 'ordered pair' (x,y) in set theory. *)
(* The pair {x,y} is essentially 'unordered' and we have {x,y} == {y,x}.        *)
Definition pair (x y:set) : set := Cons x (Cons y Nil).

(* Coq may be confused by this notation as we have already introduced '{x}'.    *)
Notation "{ x , y }" := (pair x y) : set_scope.

(* Since equality between sets is determined by their elements, this lemma      *)
(* characterizes the pair {x,y}. z is an element of {x,y} if and only if        *)
(* z == x or z == y. Use this lemma to show that {x,y} == {y,x} or {x,x} = {x}. *)
Lemma pair_charac : forall (x y z:set), z :: {x,y} <-> (z == x) \/ (z == y).
Proof.
    intros x y z. split.
    - intros H. apply toListElem in H. 
      destruct H as [z' [H1 [H2 H3]]]. destruct H1 as [H1|[H1|H1]].
        + left. apply equal_trans with z'.
            { apply doubleIncl. split; assumption. }
            { rewrite H1. apply equal_refl. }
        + right. apply equal_trans with z'.
            { apply doubleIncl. split; assumption. }
            { rewrite H1. apply equal_refl. }
        + inversion H1.
    - intros [H|H]; apply toListElem.
        + exists x. split.
            { left.  reflexivity. }
            { apply doubleIncl in H. destruct H as [H1 H2]. split; assumption. }
        + exists y. split.
            { right.  left. reflexivity. }
            { apply doubleIncl in H. destruct H as [H1 H2]. split; assumption. }
Qed.

(* The pairing axiom is satisfied in 'set': Given two sets x and y, there       *)
(* exists a set z, such that for any set u, u is an element of z if and only if *)
(* u is equal to x or u is equal to y. In other words, the pair {x,y} exists.   *)
Theorem pairing : forall (x y:set), exists (z:set), forall (u:set),
    u :: z <-> (u == x) \/ (u == y).
Proof.
    intros x y. exists {x,y}. apply pair_charac. 
Qed.

