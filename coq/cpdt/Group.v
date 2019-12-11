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

