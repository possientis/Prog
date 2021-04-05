Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

Inductive Valid (b v:Type) : @Context b v -> Prop :=
| ValidO   : Valid b v O
| ValidTy  : forall (G:Context) (Ty:b),
    Valid b v G -> Valid b v (G ; Ty ::: *)
| ValidVar : forall (G:Context) (x:v) (Ty:T b),
    Valid b v G -> G :- Ty -> Valid b v (G ; x ::: Ty) 
.

Arguments Valid    {b} {v}.
Arguments ValidO   {b} {v}.
Arguments ValidTy  {b} {v}.
Arguments ValidVar {b} {v}.

(* An example of valid context                                                  *)
Definition G1 (base v:Type) (a b:base) (const:v) : @Context base v 
    := O
    ; a ::: *
    ; b ::: *
    ; const ::: ((Base b :-> Base b) :-> Base a :-> Base b :-> Base b)
    .
Arguments G1 {base} {v}.

Lemma ValidG1 : forall (base v:Type) (a b:base) (const:v),
    Valid (G1 a b const).
Proof.
    intros base v a b const. constructor.
    - constructor. constructor. constructor.
    - constructor.
        + constructor; constructor; apply FindTyZ.
        + constructor.
            { constructor. apply FindTyS, FindTyZ. }
            { constructor; constructor; apply FindTyZ. }
Qed.

