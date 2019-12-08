Inductive type : Type :=
| Nat     : type
| NatFunc : type -> type
.

Inductive term : type -> Type :=
| Const : nat -> term Nat
| Plus  : term Nat -> term Nat -> term Nat
| Abs   : forall (t:type), (nat -> term t) -> term (NatFunc t)
.

Fixpoint typeDenote (t:type) : Type :=
    match t with
    | Nat       => nat
    | NatFunc t => nat -> typeDenote t
    end.

Fixpoint termDenote (t:type) (e:term t) : typeDenote t :=
    match e with
    | Const n       => n
    | Plus e1 e2    => termDenote _ e1 + termDenote _ e2
    | Abs _ e1      => fun x => termDenote _ (e1 x)
    end.

Arguments termDenote {t}.

(* Naive reification attempt.                                                   *)
Ltac reify1 e :=
    match e with
    | ?E1 + ?E2 =>
        let r1 := reify1 E1 in
        let r2 := reify1 E2 in
            constr:(Plus r1 r2)
    | fun (x:nat) => ?E1    =>
        let r1 := reify1 E1 in
            constr:(Abs (fun (x:nat) => r1 x))
    | _ => constr:(Const e)
    end.

(* Still won't handle recursion properly, see cpdt page 315                     *)
Ltac reify2 e :=
    match e with
    | ?E1 + ?E2 =>
        let r1 := reify2 E1 in
        let r2 := reify2 E2 in
            constr:(Plus r1 r2)
    | fun (x:nat) => @?E1 x =>   (* @?E1 followed by possible variable x        *)
        let r1 := reify2 E1 in
            constr:(Abs (fun (x:nat) => r1 x))
    | _ => constr:(Const e)
    end.

(* yeah ok, but why ....                                                        *)
Ltac reify e :=
    match eval simpl in e with
    | fun (x:?T) => @?E1 x + @?E2 x =>
        let r1 := reify E1 in
        let r2 := reify E2 in
            constr:(fun x => Plus (r1 x) (r2 x))
    | fun (x:?T)(y:nat) => @?E1 x  y =>
        let r1 := reify (fun p:T*nat => E1 (fst p) (snd p)) in
            constr:(fun u => Abs (fun v => r1 (u,v)))
    | _ =>  constr:(fun x => Const (e x))
    end.


Ltac refl :=
    match goal with
    | [|- ?E1 = ?E2] =>
        let E1' := reify (fun _ : unit => E1) in
        let E2' := reify (fun _ : unit => E2) in
            change (termDenote (E1' tt) = termDenote (E2' tt));
                cbv beta iota  delta [fst snd]
    end.

(* bollocks !                                                                   *)
Goal (fun (x y:nat) => x + y + 13) = (fun (_ z : nat) => z).
    refl.
Show.

