Definition ProdRec : forall (a b:Type) (c:a * b -> Type),
    (forall (x:a) (y:b), c (x,y)) -> forall (z:a * b), c z.
Proof.
refine (fun (a b:Type) (c:a * b -> Type) (IH:forall (x:a) (y:b), c (x,y)) =>
    fun (z:a * b) =>
        match z with
        | (x , y) => IH x y
        end
).
Defined.

Definition L1 : forall (a b:Type) (z:a * b), (fst z, snd z) = z.
Proof.
refine ( fun (a b:Type) (z:a * b) =>
    match z with
    | (x, y) => eq_refl (x,y)
    end
).
Qed.

Definition swap : forall (a b:Type), a * b -> b * a :=
    fun (a b:Type) (z:a * b) =>
        match z with
        | (x,y) => (y,x)
        end.

Arguments swap {a} {b}.

Definition L2 : forall (a b:Type) (z:a * b), swap (swap z) = z.
Proof.
refine (fun (a b:Type) (z:a * b) =>
    match z with
    | (x,y) => eq_refl (x,y)
    end
).
Qed.

Definition proj1 : forall (a b:Type) (z:a * b), a.
Proof.
refine (fun (a b:Type) => ProdRec a b (fun _ => a)
    (fun (x:a) (y:b) => x)
).
Defined.

Definition L3 : proj1 = @fst.
Proof. reflexivity. Qed.


Definition proj2 : forall (a b:Type) (z:a * b), b.
Proof.
refine (fun (a b:Type) => ProdRec a b (fun _ => b)
    (fun (x:a) (y:b) => y)
).
Defined.

Definition L4 : proj2 = @snd.
Proof. reflexivity. Qed.

Definition L5 : proj2 = @snd := eq_refl _.

Open Scope type_scope.

Definition swap' : forall (a b:Type), a * b -> b * a.
Proof.
refine(fun (a b:Type) => ProdRec a b (fun _ => (b * a)) 
    (fun (x:a) (y:b) => (y, x))
).
Defined.




