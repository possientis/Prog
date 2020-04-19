Variable Exists   : forall (a:Type), (a -> Prop) -> Prop. 
Variable mkExists : forall (a:Type) (p:a -> Prop) (x:a), p x -> Exists a p.
Variable ExistsInd : forall (a:Type) (p:a -> Prop) (c:Exists a p -> Prop), (forall (x:a)(q:p x), c (mkExists a p x q)) -> forall (e:Exists a p), c e.

Definition ExistsE : forall (a:Type) (p:a -> Prop) (A:Prop), 
    (forall (x:a), p x -> A) -> Exists a p -> A := 
    fun a p A H e => ExistsInd a p (fun _ => A) H e.

Inductive Exists2 (a:Type) (p:a -> Prop) : Prop :=
| mkExists2 : forall (x:a), p x -> Exists2 a p
.

Definition ExistsInd2 : forall (a:Type) (p:a -> Prop) (c:Exists2 a p -> Prop), 
    (forall (x:a)(q:p x), c (mkExists2 a p x q)) -> 
        forall (x:Exists2 a p), c x :=
    fun (a:Type) (p:a -> Prop) (c:Exists2 a p -> Prop) (f:forall (x:a) (q:p x), c (mkExists2 a p x q)) (e:Exists2 a p) =>
        match e with
        | mkExists2 _ _ x q => f x q
        end. 

(*
Check Exists2.

Check mkExists2.

Arguments Exists {a}.
Arguments mkExists {a} {p}.

Notation "E x , p" := (Exists p) (at level 50).


Definition L1 : forall (a:Type) (p:a -> Prop), ~(Exists p) <-> forall (x:a), ~ p x.
Proof.
    intros a p. split.
    - intros f x H. apply f. apply mkExists with x. assumption.
    - intros f H.

Show.
*)
