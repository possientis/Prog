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
| iWeak: forall G x t S T, 
        infer G t T
    (*------------------------*)
    ->  infer (G, x :: S) t T

| iBeta: forall G x t S T,
    infer G (tLam x S t) (S ~> T)
 (*-------------------------------*)
    ->  infer (G, x :: S) t T
.

Notation "G |- t $ T" := (infer G t T) (at level 20).

Lemma weakening : forall G D x t S T, 
        (G ; D) |- t $ T 
    (*---------------------------*)
    -> ((G, x :: S); D) |- t $ T.
Proof.
    intros G. induction D as [|D IH a].
    - simpl. intros x t S T H. constructor. assumption.
    - simpl. destruct a as [u U]. intros x t S T H. apply iBeta, IH, iLam.
      assumption.
Qed.
