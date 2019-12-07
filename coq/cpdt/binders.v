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
