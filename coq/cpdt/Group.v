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
    Axiom ident' : forall (a:M.G), M.f a (M.e) = a.
    Axiom inverse' : forall (a:M.G), M.f a (M.i a) = M.e.
    Axiom unique_e : forall e', (forall a, M.f e' a = a) -> e' = M.e.
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

