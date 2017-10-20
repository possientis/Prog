Record Category (A:Type) : Type := category
    {   source_  : A -> A
    ;   target_  : A -> A
    ;   compose_ : A -> A -> option A
    ;   proof_ss : forall f:A, source_ (source_ f) = source_ f    
    ;   proof_ts : forall f:A, target_ (source_ f) = source_ f
    ;   proof_tt : forall f:A, target_ (target_ f) = target_ f
    ;   proof_st : forall f:A, source_ (target_ f) = target_ f
    ;   proof_dom: forall f g:A, target_ f = source_ g <-> compose_ f g <> None
    ;   proof_src: forall f g h:A, compose_ f g = Some h -> source_ h = source_ f
    ;   proof_tgt: forall f g h:A, compose_ f g = Some h -> target_ h = target_ g
    ;   proof_idl: forall a f:A, 
            a = source_ a -> 
            a = target_ a -> 
            a = source_ f -> 
            compose_ a f = Some f
    ;   proof_idr: forall a f:A,
            a = source_ a -> 
            a = target_ a -> 
            a = target_ f -> 
            compose_ f a = Some f
    ;   proof_asc: 
            forall f g h fg gh:A, 
            compose_ f g = Some fg -> 
            compose_ g h = Some gh -> 
            compose_ f gh = compose_ fg h
    }
    .

(* implicit type argument *)
Definition source  {A:Type} (c:Category A) : A -> A := source_ A c.
Definition target  {A:Type} (c:Category A) : A -> A := target_ A c.
Definition compose {A:Type} (c:Category A) : A -> A -> option A := compose_ A c.


