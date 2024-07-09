Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Proof.

Definition andComm (v:Type) (G:Ctx v) (p q:P v): 
  G :- and p q :-> and q p
  
:= deduct 
    (andIntro 
      (andElimR extract) 
      (andElimL extract)).

Arguments andComm {v} {G} {p} {q}.

Definition orComm (v:Type) (G:Ctx v) (p q:P v): 
  G :- or p q :-> or q p

:= deduct 
    (orElim 
      (orIntroR extract) 
      (orIntroL extract) 
      extract).

Arguments orComm {v} {G} {p} {q}.

Definition pierce (v:Type) (G:Ctx v) (p q:P v): 
  G :- ((p :-> q) :-> p) :-> p

:= deduct 
    (caseof 
      extract 
      (modus 
        (deduct 
          (botElim 
            (modus 
              extract 
              (weaken extract)))) 
        (weaken extract))).

 Arguments pierce {v} {G} {p} {q}.

(* TODO: Understand why we are required to write '¬(¬p)' instead of '¬¬p' below *)
Definition classic (v:Type) (G:Ctx v) (p:P v):
  G :- ¬(¬p) :-> p
 
:= deduct 
    (reduct 
      (modus 
        extract 
        (weaken extract))).

Arguments classic {v} {G} {p}.

Definition lem (v:Type) (G:Ctx v) (p:P v):
  G :- or p ¬p

:= caseof 
    (orIntroL extract) 
    (orIntroR extract).

Arguments lem {v} {G} {p}.

Definition andToOr (v:Type) (G:Ctx v) (p q:P v):
  G :- ¬(and ¬p ¬q) :-> or p q

:= deduct 
    (caseof 
      (orIntroL extract) 
      (caseof 
        (orIntroR extract) 
        (botElim 
          (modus 
            (andIntro 
              (weaken extract) 
              extract) 
            (weaken (weaken extract)))))).

Arguments andToOr {v} {G} {p} {q}.

Definition impToOr (v:Type) (G:Ctx v) (p q:P v):
  G :- (p :-> q) :-> or ¬p q

:= deduct 
    (caseof 
      (orIntroR 
        (modus 
          extract 
          (weaken extract))) 
      (orIntroL extract)).

Arguments impToOr {v} {G} {p} {q}.

