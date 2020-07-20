Require Import List.

Require Import Utils.LEM.

Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Incl.
Require Import Core.Equal.
Require Import Core.Compatible.

Require Import Lang1.Syntax.
Require Import Lang1.Apply.
Require Import Lang1.Semantics.
Require Import Lang1.Relevance.
Require Import Lang1.Environment.

(* Theorem schema of specification expressed in set theory abstract syntax.     *)
(* The formulation is parameterized with respect to a formula P, hence this is  *)
(* not a single theorem, but rather a 'theorem schema'. This formulation is     *)
(* correct provided the variables n m p are distinct and m is not free in P.    *)
Definition specificationF (P:Formula) (n m p:nat) : Formula :=
    All n (Exi m (All p (Iff (Elem p m) (And (Elem p n) P)))). 

(* Evaluating specificationF applied to a formula P in any environment 'yields' *)
(* the theorem specificationDec' applied to the corresponding predicate.        *)
Lemma evalSpecificationF : LEM -> forall (e:Env) (P: Formula) (n m p:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    ~In m (free P) ->
    eval e (specificationF P n m p)
        <->
    forall (x:set), exists (y:set), forall (z:set),
        z :: y <-> z :: x /\ (eval2 e P n p x z).
Proof.
    intros L e P n m p Hmn Hpn Hpm NF. unfold specificationF. rewrite evalAll.
    split; intros H x. 
    - remember (H x) as H' eqn:E. clear E H. rewrite evalExi in H'.
      destruct H' as [y H]. exists y. rewrite evalAll in H. intros z.
      remember (H z) as H' eqn:E. clear E H. rewrite evalIff in H'.
      rewrite evalElem in H'. rewrite evalAnd in H'. rewrite evalElem in H'.
      rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
      rewrite bindDiff in H'. rewrite bindDiff in H'. rewrite bindSame in H'.
      unfold eval2. destruct H' as [H1 H2]. split.
        + rewrite <- (evalNotInFree (bind (bind e n x) p z)).
            { rewrite (evalEnvEqual _ (bind (bind (bind e n x) m y) p z)). 
                { assumption. }
                { apply bindPermute. 
                  intros Hmp. apply Hpm. symmetry. assumption. }}
            { assumption. }
        + intros [H3 H4]. apply H2. split.
            { assumption. }
            { rewrite (evalEnvEqual _ (bind (bind (bind e n x) p z) m y)).
                { rewrite evalNotInFree; assumption. }
                { apply bindPermute. assumption. }}
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - rewrite evalExi. remember (H x) as H' eqn:E. clear E H.
      destruct H' as [y H]. exists y. rewrite evalAll. intros z.
      rewrite evalIff, evalElem, evalAnd, evalElem, bindSame.
      rewrite bindDiff, bindSame, bindDiff, bindDiff, bindSame. 
      remember (H z) as H' eqn:E. clear E H. unfold eval2 in H'. split.
        + destruct H' as [H1 _]. intros H'.
          remember (H1 H') as H eqn:E. clear E H1 H'. 
          destruct H as [H1 H2]. split.
            { assumption. }
            { rewrite (evalEnvEqual _ (bind (bind (bind e n x) p z) m y)).
                { rewrite evalNotInFree; assumption. }
                { apply bindPermute. assumption. }}
        + destruct H' as [_ H]. intros [H1 H2]. apply H. split.
            { assumption. }
            { rewrite (evalEnvEqual _ (bind (bind (bind e n x) p z) m y)) in H2.
                { rewrite evalNotInFree in H2; assumption. }
                { apply bindPermute. assumption. }}
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.


(* Theorem schema of specification where we explicitely 'apply' P at the        *)
(* variables n and  p with 'apply2 P n p'.                                      *)
Definition specificationF' (P:Formula) (n m p:nat) : Formula :=
    All n (Exi m (All p (Iff (Elem p m) (And (Elem p n) (apply2 P n p))))). 

(* Checking that the only difference between these statements is the apply2.    *)
Lemma specificationLink : forall (P:Formula) (n m p:nat),
    specificationF' P n m p = specificationF (apply2 P n p) n m p.
Proof.
    intros P n m p. reflexivity.
Qed.


