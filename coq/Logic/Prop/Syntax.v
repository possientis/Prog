Require Import List.

Declare Scope Prop_Syntax_scope.

(* Given a type v of all propositional variables, defines the tyoe P v of all   *)
(* formulas of propositional logic with atoms in v                              *)
Inductive P (v:Type) : Type :=
| Bot : P v
| Var : v -> P v
| Imp : P v -> P v -> P v
.

Arguments Bot {v}.
Arguments Var {v}.
Arguments Imp {v}.

Notation "p :-> q" := (Imp p q)
  (at level 20, right associativity)  : Prop_Syntax_scope.

Notation "¬ p" := (Imp p Bot)
  (at level 1, no associativity)      : Prop_Syntax_scope.

Notation "' p" := (Var p)
  (at level 1, no associativity)      : Prop_Syntax_scope.

Definition bot (v:Type) : P v := Bot.

Arguments bot {v}.

(* A context is a list of propositions. No need to create a 'snoc' version for  *)
(* this, we simply need to remember new formulas are 'cons'-ed to the left      *)
Definition Ctx (v: Type) : Type := list (P v).

Notation "G ; p" := (cons p G)
  (at level 50, left associativity) : Prop_Syntax_scope.
     
Open Scope Prop_Syntax_scope.

(* Extract: construct a proof of the sequent G;p :- p                           *)
(* So that a formula p is provable from a context with p itself as its head     *)
(*                                                                              *)
(* Deduct: given a proof of the sequent G;p :- q , provides a proof of the      *)
(* sequent G :- p -> q. So p -> q is provable in context G if q is provable     *)
(* in context G;p                                                               *)
(*                                                                              *)
(* Modus : aka modus ponens, combines a proof of the sequent G :- p and a       *)
(* proof of the sequent G :- p -> q to create a proof of the sequent G :- q     *)
(* So q is provable under G if both p and p -> q are                            *)
(*                                                                              *)
(* Reduct: aka RAA or Reductio ad absurdum, creates a proof of the sequent      *)
(* G :- p from a proof of the sequent G;¬p :- Bot                               *)
(* So if bottom is provable from a context G, having assumed ¬p, then p is      *)
(* provable from the context G                                                  *)
(*                                                                              *)
(* Weaken: creates a proof of G;q :- p from a proof of G :- p                   *)
(* So if p is provable under G, it is provable under the larger context G;q     *)

Inductive Seq (v:Type) : Ctx v -> P v -> Type :=
| Extract:forall (G:Ctx v)(p:P v),    Seq v (G;p) p 
| Weaken: forall (G:Ctx v)(p q:P v),  Seq v G p -> Seq v (G;q) p
| Deduct: forall (G:Ctx v)(p q:P v),  Seq v (G;p) q -> Seq v G (p :-> q)
| Modus:  forall (G:Ctx v)(p q: P v), Seq v G p -> Seq v G (p :-> q) -> Seq v G q
| Reduct: forall (G:Ctx v)(p:P v),    Seq v (G;¬p) bot -> Seq v G p
.

Arguments Seq {v}.
Arguments Extract {v}.
Arguments Deduct {v}.
Arguments Modus {v}.
Arguments Reduct {v}.
Arguments Weaken {v}.

Notation "G :- p" := (Seq G p)
  (at level 90, no associativity) : Prop_Syntax_scope.

Definition extract (v:Type) (G:Ctx v) (p:P v) : G;p :- p 
  := Extract G p. 

Arguments extract {v} {G} {p}.

Definition deduct (v:Type) (G:Ctx v) (p q:P v) : (G;p :- q) -> (G :- p :-> q)
  := Deduct G p q.

Arguments deduct {v} {G} {p} {q}.

Definition modus (v:Type)(G:Ctx v)(p q:P v): (G :- p) -> (G :- p :-> q) -> G :- q
  := Modus G p q.

Arguments modus {v} {G} {p} {q}.

Definition reduct (v:Type) (G:Ctx v) (p:P v) : (G;¬p :- bot) -> (G :- p)
  := Reduct G p.

Arguments reduct {v} {G} {p}.

Definition weaken (v:Type) (G:Ctx v) (p q:P v) : (G :- p) -> (G;q :- p)
  := Weaken G p q.

Arguments weaken {v} {G} {p} {q}.

Definition or (v:Type) (p q: P v) : P v := ¬p :-> q.

Arguments or {v}.

Definition and (v:Type) (p q: P v) : P v := ¬(or ¬p ¬q).

Arguments and {v}.

(* Builds a proof of anything from a proof of bottom                            *)
(* We start from e : G :- bot                                                   *)
(* After weakening we obtain G;¬p :- bot                                        *)
(* from which we obtain G :- p by reduction ad absurdum                         *)
Definition exbot (v:Type) (G:Ctx v) (p:P v) (e:G :- bot) : G :- p 
  := reduct (weaken e).

Arguments exbot {v} {G} {p}.

(* Reverses the effect of deduction: creates a proof of                         *)
(* q in context G;p from a proof of p -> q in context G                         *)
(* We start from e : G :- p -> q                                                *)
(* By extraction we have G;p :- p                                               *)
(* By weakening we have G;p :- p -> q                                           *)
(* We conclude from modus ponens that G;p :- q                                  *)
Definition revdeduct (v:Type) (G:Ctx v) (p q:P v) (e:G :- p :-> q) : G;p :- q
  := modus extract (weaken e).

Arguments revdeduct {v} {G} {p} {q}.

(* Builds a proof of G;q;p :- r, given a proof of G;p;q :-r                     *)
(* This function allows us to switch the order of the two front assumptions     *)
(* We start with e : G;p;q :- r                                                 *)
(* By double deduction and double weakening we obtain:                          *)
(* G;q;p :- p -> q -> r                                                         *)
(* By extraction we have G;q;p :- p                                             *)
(* Hence using modus ponens we have G;q;p :- q -> r                             *)
(* However, by extraction followed by weakening we have G;q;p :- q              *)
(* So using modus ponens once more we obtain G;q;p :-r                          *)
Definition switch (v:Type) (G:Ctx v) (p q r:P v) (e:G;p;q :- r) : G;q;p :- r
  := modus 
      (weaken extract) 
      (modus 
        extract 
        (weaken (weaken (deduct (deduct e))))).

Arguments switch {v} {G} {p} {q} {r}.
         
(* Builds a proof of G;¬q :- ¬p from a proof of G;p :- q                        *)
(* Modulo deduction, this is the same as building a proof of ¬q -> ¬p from a    *)
(* a proof of p -> q.                                                           *)
(* We start from e : G;p :- q                                                   *)
(* By deduction and double weakening we obtain G;¬q;p :- p -> q                 *)
(* By extraction we have G;¬q;p :- p                                            *)
(* Hence using modus ponens we obtain G;¬q;p :- q                               *)
(* However, from extraction followed by weakening we have G;¬q;p :- q -> bot    *)
(* Using modus ponens once more we obtain G;¬q;p :- bot                         *)
(* We conclude from deduction that G;¬q :- ¬p                                   *)
Definition contra (v:Type) (G:Ctx v) (p q:P v) (e:G;p :- q) : G;¬q :- ¬p
  := deduct 
      (modus 
        (modus 
          extract 
          (weaken (weaken (deduct e)))) 
        (weaken extract)).

Arguments contra {v} {G} {p} {q}.

(* Builds a proof of G :- q given proofs of G;p :- q and G;¬p :- q              *)
(* This allows us to build proofs with a case analysis on p                     *)
(* We start with e1 : G;p :- q and e2 : G;¬p :- q                               *)
(* By using contra on e1 we have G;¬q :- ¬p                                     *)
(* By deduction on e2 followed by weakening we have G;¬q :- ¬p -> q             *)
(* Hence from modus ponens we obtain G;¬q :- q                                  *)
(* However we also have G;¬q :- q -> bot by extraction                          *)
(* Using modus ponens once more, we have G;¬q :- bot                            *)
(* It follows by reduction that G :- q                                          *)
Definition caseof (v:Type)(G:Ctx v)(p q:P v)(e1:G;p :- q)(e2:G;¬p :- q) : G :- q
  := reduct 
      (modus 
        (modus 
          (contra e1) 
          (weaken (deduct e2))) 
        extract).

Arguments caseof {v} {G} {p} {q}.

(* Builds a proof of G;p\/q :- r from proofs of G;p :- r and G;q :- r           *)
(* We start from e1 : G;p :- r and e2 : G;q :-r                                 *)
(* We want to obtain a proof of G;p\/q :- r                                     *)
(* Using a case analysis on p, it is sufficient to obtain:                      *)
(* 1. a proof of G;p\/q;p :- r                                                  *)
(* 2. a proof of G;p\/q;¬p :- r                                                 *)
(* By deduction followed by double weakening on e1 we have G;p\/q;p :- p -> r   *)
(* By extraction we have G;p\/q;p :- p                                          *)
(* Hence 1. is obtained using modus ponens.                                     *)
(* By deduction followed by double weakening on e2 we have G;p\/q;¬p :- q -> r  *)
(* Hence using modus ponens, we only need to prove 3. G;p\/q;¬p :- q            *)
(* However by extraction we have G;p\/q;¬p :- ¬p                                *)
(* And by extraction followed by weakening we have G;p\/q;¬p :- ¬p -> q         *)
(* So 3. is obtained by virtue of modus ponens.                                 *)
Definition either (v:Type)(G:Ctx v)(p q r:P v)
  (e1:G;p :- r) (e2:G;q :- r) : G;or p q :- r
  := caseof 
      (modus 
        extract 
        (weaken (weaken (deduct e1)))) 
      (modus 
        (modus 
          extract 
          (weaken extract)) 
        (weaken (weaken (deduct e2)))).

Arguments either {v} {G} {p} {q} {r}.

(* Left introduction rule for disjunction                                       *)
(* Builds a proof of p \/ q from a proof of p                                   *)
(* We start from e : G :- p                                                     *)
(* By weakening we have G;¬p :- p                                               *)
(* By extraction we have G;¬p :- p -> bot                                       *)
(* By modus ponens we obtain G;¬p :- bot                                        *)
(* By exbot we obtan G;¬p :- q                                                  *)
(* By deduction we conclude that G :- ¬p -> q                                   *)
Definition orIntroL (v:Type) (G:Ctx v) (p q:P v) (e:G :- p) : G :- or p q
  := deduct (exbot (modus (weaken e) extract)).

Arguments orIntroL {v} {G} {p} {q}.

(* Right introduction rule for disjunction                                      *)
(* Builds a proof of p \/ q from a proof of q                                   *)
(* We start from e : G :- q                                                     *)
(* By weakening we have G;¬p :- q                                               *)
(* By deduction we conclude that G :- ¬p -> q                                   *)
Definition orIntroR (v:Type) (G:Ctx v) (p q:P v) (e:G :- q) : G :- or p q
  := deduct (weaken e).

Arguments orIntroR {v} {G} {p} {q}.

(* Disjunction elimination                                                      *)
(* Builds a proof G :- r given proofs of G;p :- r, G;q :- r and G :- p \/ q     *)
(* We start with e1 : G;p :- r,  e2 : G;q :- r and e : G :- p\/q                *)
(* Using either on e1 e2 we obtain G;p\/q :- r                                  *)
(* Using deduction we therefore get G :- p\/q -> r                              *)
(* Using modus ponens and e we finally obtain G :- r as desired                 *)
Definition orElim (v:Type) (G:Ctx v) (p q r:P v) 
  (e1:G;p :- r) (e2:G;q :- r) (e:G :- or p q) : G :- r
  := modus e (deduct (either e1 e2)).

Arguments orElim {v} {G} {p} {q} {r}.
