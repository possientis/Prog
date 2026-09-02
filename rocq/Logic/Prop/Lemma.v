Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Proof.

Definition andComm (v:Type) (G:Ctx v) (p q:P v):
  G :- and p q :-> and q p

:= deduct
    (andIntro
      (andElimR fromHyp)
      (andElimL fromHyp)).

Arguments andComm {v} {G} {p} {q}.

Definition orComm (v:Type) (G:Ctx v) (p q:P v):
  G :- or p q :-> or q p

:= deduct
    (orElim
      (orIntroR fromHyp)
      (orIntroL fromHyp)
      fromHyp).

Arguments orComm {v} {G} {p} {q}.

Definition pierce (v:Type) (G:Ctx v) (p q:P v):
  G :- ((p :-> q) :-> p) :-> p

:= deduct
    (caseof
      fromHyp
      (modus
        (deduct
          (botElim
            (modus
              fromHyp
              (weaken fromHyp))))
        (weaken fromHyp))).

 Arguments pierce {v} {G} {p} {q}.

(* TODO: Understand why we are required to write '¬(¬p)' instead of '¬¬p' below *)
Definition classic (v:Type) (G:Ctx v) (p:P v):
  G :- ¬(¬p) :-> p

:= deduct
    (reduct
      (modus
        fromHyp
        (weaken fromHyp))).

Arguments classic {v} {G} {p}.

Definition lem (v:Type) (G:Ctx v) (p:P v):
  G :- or p ¬p

:= caseof
    (orIntroL fromHyp)
    (orIntroR fromHyp).

Arguments lem {v} {G} {p}.

Definition andToOr (v:Type) (G:Ctx v) (p q:P v):
  G :- ¬(and ¬p ¬q) :-> or p q

:= deduct
    (caseof
      (orIntroL fromHyp)
      (caseof
        (orIntroR fromHyp)
        (botElim
          (modus
            (andIntro
              (weaken fromHyp)
              fromHyp)
            (weaken (weaken fromHyp)))))).

Arguments andToOr {v} {G} {p} {q}.

Definition impToOr (v:Type) (G:Ctx v) (p q:P v):
  G :- (p :-> q) :-> or ¬p q

:= deduct
    (caseof
      (orIntroR
        (modus
          fromHyp
          (weaken fromHyp)))
      (orIntroL fromHyp)).

Arguments impToOr {v} {G} {p} {q}.

