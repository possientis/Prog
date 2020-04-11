Definition ProdRec : forall (a b:Type) (c:a * b -> Type),
    (forall (x:a) (y:b), c (x,y)) -> forall (z:a * b), c z.
Proof.
refine (fun (a b:Type) (c:a * b -> Type) (IH:forall (x:a) (y:b), c (x,y)) =>
    fun (z:a * b) =>
        match z with
        | (x , y) => IH x y
        end
).
Qed.
