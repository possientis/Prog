Definition curry (a b c:Type) (f: a * b -> c) (x:a)(y:b) : c := f (x,y).

Arguments curry {a} {b} {c} _ _ _.

Definition uncurry (a b c:Type) (f: a -> b -> c) (p: a * b) : c :=
    match p with 
    | (x,y) => f x y
    end.
 
Arguments uncurry {a} {b} {c} _ _.

(*
Check @curry.
Check @uncurry.
*)

Theorem uncurry_curry : forall (a b c:Type) (f: a * b -> c) (p:a * b),
    uncurry (curry f) p = f p.
Proof. destruct p as [x y]. reflexivity. Qed.

Theorem curry_uncurry : forall (a b c:Type) (f: a -> b -> c) (x:a) (y:b),
    curry (uncurry f) x y = f x y.
Proof. reflexivity. Qed.

