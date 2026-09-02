(*
Module Type GROUP.
    Parameter G   : Set.
    Parameter f   : G -> G -> G.
    Parameter e   : G.
    Parameter i   : G -> G.
    Axiom assoc   : forall (a b c:G), f (f a b) c = f a (f b c).
    Axiom ident   : forall (a:G), f e a = a.   (* left identity enough ? *)
    Axiom inverse : forall (a:G), f (i a) a = e.    (* left side enough ? *)
End GROUP.

Module Type GROUP_THEOREMS.
    Declare Module M : GROUP.
    Import M.
    Axiom ident' : forall (a:M.G), M.f a (M.e) = a.
    Axiom inverse' : forall (a:G), f a (i a) = e.   (* Import M !! *)
    Axiom unique_e : forall e', (forall a, f e' a = a) -> e' = e.
End GROUP_THEOREMS.

Module GROUP_PROOFS (M:GROUP) : GROUP_THEOREMS with Module M := M.
Module M := M.
Import M.

Theorem inverse' : forall a, f a (i a) = e.
Proof.
    intros a.
    rewrite <- (ident (f a (i a))).
    remember (f e (f a (i a))) as x eqn:E.
    rewrite <- (inverse (f a (i a))) in E.
    rewrite assoc in E.
    rewrite assoc in E.
    rewrite <- (assoc (i a) a (i a)) in E.
    rewrite inverse in E.
    rewrite ident in E.
    rewrite inverse in E.
    assumption.
Qed.

Theorem ident' : forall (a:G), f a e = a.
Proof.
    intros a.
    rewrite <- (inverse a).
    rewrite <- assoc.
    rewrite inverse'.
    rewrite ident.
    reflexivity.
Qed.


Theorem unique_e : forall (e':G), (forall (a:G), f e' a = a) -> e' = e.
Proof.
    intros e' H. rewrite <- (ident' e'), H. reflexivity.
Qed.
End GROUP_PROOFS.

Require Import ZArith.
Open Scope Z_scope.
Module INT.
    Definition G := Z.
    Definition f x y := x + y.
    Definition e := 0.
    Definition i x := -x.
    Theorem assoc : forall a b c, f (f a b) c = f a (f b c).
    Proof. intros a b c. unfold f. ring. Qed.
    Theorem ident : forall a, f e a = a.
    Proof. intros a. unfold f. unfold e. ring. Qed.
    Theorem inverse : forall a, f (i a) a = e.
        intros a. unfold f, i, e. ring. Qed.
End INT.

Module INT_PROOFS := GROUP_PROOFS(INT).
Import INT_PROOFS.
*)
(* Check unique_e. *)








