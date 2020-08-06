Require Import List.  
Require Import Logic.Class.Eq.
Require Import Logic.Axiom.LEM.
Require Import Logic.Func.Replace.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Subformula.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Compatible.

Require Import Logic.Lang1.Apply.
Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Relevance.
Require Import Logic.Lang1.Environment.

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
    ~In m (Fr P) ->
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
Local Lemma specificationLink_ : forall (P:Formula) (n m p:nat),
    specificationF' P n m p = specificationF (apply2 P n p) n m p.
Proof.
    intros P n m p. reflexivity.
Qed.

(* Helper lemma used in next result.                                            *)
Local Lemma specificationCarryOver_ : forall (p q: set -> set -> Prop),
    (forall (x y:set), p x y <-> q x y) ->
        (forall (x:set), exists (y:set), forall (z:set),
            z :: y <-> z :: x /\ p x z)
    <-> (forall (x:set), exists (y:set), forall (z:set),
            z :: y <-> z :: x /\ q x z).
Proof.
    intros p q H1. split; intros H2 x; destruct (H2 x) as [y H3]; exists y;
    intros z; destruct (H3 z) as [H4 H5]; split.
    - intros H6. destruct (H4 H6) as [H7 H8]. split.
        + assumption.
        + apply H1. assumption.
    - intros [H6 H7]. apply H5. split.
        + assumption.
        + apply H1. assumption.
    - intros H6. destruct (H4 H6) as [H7 H8]. split.
        + assumption.
        + apply H1. assumption.
    - intros [H6 H7]. apply H5. split.
        + assumption.
        + apply H1. assumption.
Qed.

(* Evaluating specificationF' applied to a formula P in any environment yields  *)
(* the expected statement. However, due to the way we defined 'apply2' where    *)
(* the variable 0 and 1 have this special role, instead of having 'n' and 'p'   *)
(* bound to the values x and z, we must have '0' and '1' bound to x and z. This *)
(* is reflected by 'eval2 e P 0 1 x z'. Note that we cannot obtain this result  *)
(* without making some assumptions on the variables n m p. As before, we need   *)
(* n m and p to be distinct, and we need ~ In m (Fr P). But we also need the    *)
(* replacement of 0 and 1 by n and p to be a valid substitution in P. We also   *)
(* cannot expect this replacement to have the correct semantics if n and p are  *)
(* already free variables of P. Hence the ~In n (Fr P) and ~In p (Fr P).        *)
Lemma evalSpecificationF' : LEM -> forall (e:Env) (P: Formula) (n m p:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    ~In m (Fr P) ->
    ~In n (Fr P) ->
    ~In p (Fr P) ->
    valid (replace2 0 1 n p) P ->
    eval e (specificationF' P n m p)
        <->
    forall (x:set), exists (y:set), forall (z:set),
        z :: y <-> z :: x /\ (eval2 e P 0 1 x z).
Proof.
    intros L e P n m p H1 H2 H3 H4 H5 H6 H7. rewrite specificationLink_. 
    rewrite evalSpecificationF. apply specificationCarryOver_.
    intros x y. apply evalApply2.
    - assumption.
    - exact H5.         (* <- H5 *)
    - exact H6.         (* <- H6 *)
    - intros H8. subst. apply H2. reflexivity.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - unfold apply2. remember (replace2 0 1 n p) as f eqn:E.
      assert (Fr (fmap f P) = map f (Fr P)) as H8.
        { apply (valid_free nat nat _ _ f P).
            { assumption. }
            { apply Sub_refl. }}
      rewrite H8. intros H9. apply in_map_iff in H9. destruct H9 as [x [H9 H10]].
      clear H8 H7. rewrite E in H9. clear E f. unfold replace2 in H9.
      destruct (eqDec x 0) as [H11|H11].
        + subst. apply H1. reflexivity.
        + destruct (eqDec x 1) as [H12|H12].
            { subst. apply H3. reflexivity. }
            { rewrite H9 in H10. 
              apply H4. (* <- H4 *)
              assumption. }
Qed.
