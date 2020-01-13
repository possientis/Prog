Inductive type : Type :=
| base  : type
| arrow : type -> type -> type
.

Notation "a ~> b" := (arrow a b) (at level 20, b at next level).

Inductive assumption : Type :=
| assume : nat -> type -> assumption
.

Notation "x :: t" := (assume x t).

Inductive ctx : Type :=
| empty : ctx
| snoc  : ctx -> assumption -> ctx
.

Notation "G , a" := (snoc G a) (at level 70, a at next level).


Fixpoint conc (G D:ctx) : ctx :=
    match D with
    | empty     => G
    | snoc D' x => snoc (conc G D') x
    end.

Notation "G ; D" := (conc G D) (at level 20).

Inductive term : Type := 
| tVar : nat  -> type -> term
| tApp : term -> term -> term
| tLam : nat  -> type -> term -> term 
.

Inductive infer : ctx -> term -> type -> Prop :=
| iWeak: forall G x t S T, 
        infer G t T
    (*------------------------*)
    ->  infer (G, x :: S) t T

| iVar: forall G x T, 
    (*------------------------*)
        infer G (tVar x T) T

| iApp: forall G s t S T, 
        infer G t (S ~> T) -> infer G s S
    (*-------------------------------------*)
    ->  infer G (tApp t s) T

| iLam: forall G x t S T,  
        infer (G, x :: S) t T
    (*--------------------------------*)
    ->  infer G (tLam x S t) (S ~> T)
.

Notation "G |- t $ T" := (infer G t T) (at level 20).

(*
Inductive term : ctx -> type -> Type :=
| ax    : forall G t, term (G,t) t
| weak  : forall G t, term G t -> forall s, term (G,s) t
| abs   : forall G t s, term (G,t) s -> term G (t ~> s)
| app   : forall G t s, term G (t ~> s) -> term G t -> term G s 
.
*)

Lemma weakening : forall G D x t S T, 
        (G ; D) |- t $ T 
    (*---------------------------*)
    -> ((G, x :: S); D) |- t $ T.
Proof.
(*
    intros G D t H. remember (G ; D) as E eqn:Ectx. revert Ectx. revert G D.
    induction H as [ | | | ].
    - intros G' D H s. revert H. induction D as [|D x].
        + simpl. intros H. rewrite <- H.
*)

Show.

