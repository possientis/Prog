Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

Inductive Valid (b v:Type) : @Context b v -> Prop :=
| ValidO   : Valid b v O
| ValidTy  : forall (G:Context) (t:b),
    Valid b v G -> Valid b v (G ; t ::: *)
| ValidVar : forall (G:Context) (x:v) (Ty:T b),
    Valid b v G -> G :- Ty -> Valid b v (G ; x ::: Ty) 
.

Arguments Valid    {b} {v}.
Arguments ValidO   {b} {v}.
Arguments ValidTy  {b} {v}.
Arguments ValidVar {b} {v}.

(* An example of valid context                                                  *)
Definition G1 (b v:Type) (t t':b) (const:v) : @Context b v 
    := O
    ; t  ::: *
    ; t' ::: *
    ; const ::: ((Base t' :-> Base t') :-> Base t :-> Base t' :-> Base t')
    .
Arguments G1 {b} {v}.

Lemma ValidG1 : forall (b v:Type) (t t':b) (const:v),
    Valid (G1 t t' const).
Proof.
    intros b v t t' const. constructor.
    - constructor. constructor. constructor.
    - constructor.
        + constructor; constructor; apply FindTyZ.
        + constructor.
            { constructor. apply FindTyS, FindTyZ. }
            { constructor; constructor; apply FindTyZ. }
Qed.

