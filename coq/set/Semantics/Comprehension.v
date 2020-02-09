Require Import List.

Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Incl.
Require Import Core.Equal.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Compatible.
Require Import Core.Environment.

(* Theorem schema 'comprehensionLEM' expressed in set theory abstract syntax.   *)
(* The formulation is parameterized with respect to a formula P, hence this is  *)
(* not a single theorem, but rather a 'theorem schema'. This formulation is     *)
(* correct provided the variables n m p are distinct and m is not free in P.    *)


Definition comprehensionF (P : Formula) (n m p:nat) : Formula :=
    All n (Exi m (All p (Iff (Elem p m) (And (Elem p n) P)))). 

Lemma evalComprehensionF : LEM -> forall (e:Env) (P: Formula) (n m p:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    ~In m (free P) ->
    eval e (comprehensionF P n m p)
        <->
    forall (x:set), exists (y:set), forall (z:set),
        z :: y <-> z :: x /\ (eval' e p P z).
Proof.
    intros L e P n m p Hmn Hpn Hpm NF. unfold comprehensionF. rewrite evalAll.
    split; intros H x. 
    - remember (H x) as H' eqn:E. clear E H. rewrite evalExi in H'.
      destruct H' as [y H]. exists y. rewrite evalAll in H. intros z.
      remember (H z) as H' eqn:E. clear E H. rewrite evalIff in H'.
      rewrite evalElem in H'. rewrite evalAnd in H'. rewrite evalElem in H'.
      rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
      rewrite bindDiff in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
      unfold eval'.

Show.

