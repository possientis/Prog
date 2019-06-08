Definition ret (a:Type) (x:a) : option a := Some x.

Arguments ret {a} _.

Definition bind (a b:Type) (k:option a) (f:a -> option b) : option b :=
    match k with
    | None      => None
    | Some x    =>
        match (f x) with
        | None      => None
        | Some y    => Some y
        end
    end.

Arguments bind {a} {b} _ _.

Notation "k >>= f" := (bind k f) (at level 50, left associativity).

Notation "x <- k ; k'" := (k >>= (fun x => k')) 
    (at level 60, right associativity).

Definition ap (a b:Type) (f:a -> b) (x:a) : b := f x.

Arguments ap {a} {b} _ _.

Notation "f $ x" := (ap f x) (at level 60).

Definition guard (b:bool) : option (b = true) :=
    match b return option (b = true) with
    | true  => Some eq_refl
    | false => None
    end.

Definition fmap (a b:Type) (f:a -> b) (x:option a) : option b :=
    match x with
    | None      => None
    | Some x    => Some (f x)
    end.
Arguments fmap {a} {b} _ _.

Notation "f <$> x" := (fmap f x) (at level 60).


