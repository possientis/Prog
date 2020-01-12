Inductive type : Type :=
| base  : type
| arrow : type -> type -> type
.

Notation "a ~> b" := (arrow a b) (at level 20, b at next level).

Inductive ctx : Type :=
| empty : ctx
| snoc  : ctx -> type -> ctx
.

Notation "G , tau" := (snoc G tau) (at level 20, tau at next level).


Fixpoint conc (G D:ctx) : ctx :=
    match D with
    | empty     => G
    | snoc D' x => snoc (conc G D') x
    end.

Notation "G ; D" := (conc G D) (at level 20).


Inductive term : ctx -> type -> Type :=
| ax    : forall G t, term (G,t) t
| weak  : forall G t, term G t -> forall s, term (G,s) t
| abs   : forall G t s, term (G,t) s -> term G (t ~> s)
| app   : forall G t s, term G (t ~> s) -> term G t -> term G s 
.

Lemma weakening : forall G D t, term (G ; D) t -> forall s, term (G, s; D) t.
Proof.
    intros G D t H. remember (G ; D) as E eqn:Ectx. revert Ectx. revert G D.
    induction H as [ | | | ].
    - intros G' D H s. revert H. induction D as [|D x].
        + simpl. intros H. rewrite <- H.

Show.
