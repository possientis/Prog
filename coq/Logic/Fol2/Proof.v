Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Permute.

Require Import Logic.List.In.
Require Import Logic.List.Include.
Require Import Logic.List.Remove.



Require Import Logic.Fol.Free.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Syntax.

Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Axiom.

Declare Scope Fol2_Proof_scope.

(* Given a type v of variables and a decidable equality e on v, given a context *)
(* G and proposition p, we define the type 'Seq v e G p', aka 'Seq G p' as the  *)
(* type of all set theoretic proofs that the proposition p is true in context G *)
(* In fact we denote 'Seq G p' as 'G :- p', so values of type 'G :- p' are all  *)
(* possible proofs that the sequent G :- p holds.                               *)
(* If the sequent G :- p does not hold, then the type 'G :- p' is void.         *)
Inductive Seq (v:Type) (e:Eq v) : Ctx v -> P v -> Type :=
| Extract:forall (G:Ctx v)(p:P v),      CtxVal G -> Fr p <= Fr' G -> Seq v e (G;p) p
| WeakenV:forall (G:Ctx v)(x:v)(p:P v), ~(x :: Fr' G) -> Seq v e G p -> Seq v e (G,x) p
| WeakenP:forall (G:Ctx v)(p q:P v),    Fr q <= Fr' G -> Seq v e G p -> Seq v e (G;q) p
| Deduct :forall (G:Ctx v)(p q:P v),    Seq v e (G;p) q -> Seq v e G (p :-> q)
| Modus  :forall (G:Ctx v)(p q: P v),   Seq v e G p -> Seq v e G (p :-> q) -> Seq v e G q
| Reduct :forall (G:Ctx v)(p:P v),      Seq v e (G;¬p) bot -> Seq v e G p
| AxiomP :forall (G:Ctx v)(p:P v),      CtxVal G -> IsAxiom p -> Seq v e G p
| General:forall (G:Ctx v)(x:v)(p:P v), Seq v e (G,x) p -> Seq v e G (All x p)
| Special:forall (G:Ctx v)(x y:v)(p:P v),
    ~ (y :: Fr' G) -> Seq v e G (All x p) -> Seq v e (G,y) (fmap (y <:> x) p)
.

Arguments Seq     {v} {e}.
Arguments Extract {v} {e}.
Arguments WeakenV {v} {e}.
Arguments WeakenP {v} {e}.
Arguments Deduct  {v} {e}.
Arguments Modus   {v} {e}.
Arguments Reduct  {v} {e}.
Arguments AxiomP  {v} {e}.
Arguments General {v} {e}.
Arguments Special {v} {e}.

Notation "G :- p" := (Seq G p)
  (at level 90, no associativity) : Fol2_Proof_scope.

Open Scope Fol2_Proof_scope.

(* If a sequent has a proof, then its context is valid. In other words, it is   *)
(* impossible to prove a proposition from an invalid context                    *)
Lemma validContext : forall (v:Type) (e:Eq v) (G:Ctx v) (p:P v),
  G :- p -> CtxVal G.
Proof.
  intros v e G p HSeq.
  induction HSeq as
    [G p HVal HIncl
    |G x p HScope HSeq IH
    |G p q HIncl  HSeq IH
    |G p q HSeq IH
    |G p q HSeq1 IH1 ISeq2 IH2
    |G p HSeq IH
    |G p HVal HAxi
    |G x p HSeq IH
    |G x y p HScope HSeq IH].

    - constructor.
      + apply HIncl.
      + apply HVal.
    - constructor.
      + apply HScope.
      + apply IH.
    - constructor.
      + apply HIncl.
      + apply IH.
    - apply validInvertP with p, IH.
    - apply IH1.
    - apply validInvertP with ¬p, IH.
    - apply HVal.
    - apply validInvertV with x, IH.
    - constructor.
      + apply HScope.
      + apply IH.
Qed.

(* If a sequent has a proof, then all free variables of its conclusion are free *)
(* variables of its context. In other words, it is impossible to prove a        *)
(* proposition whose free variables are not in scope                            *)
Lemma freeVarsInScope : forall (v:Type) (e:Eq v) (G:Ctx v) (p:P v),
  G :- p -> Fr p <= Fr' G.
Proof.
  intros v e G p HSeq.
  induction HSeq as
    [G p HVal HIncl
    |G x p HScope HSeq IH
    |G p q HIncl  HSeq IH
    |G p q HSeq IH
    |G p q HSeq1 IH1 ISeq2 IH2
    |G p HSeq IH
    |G p HVal HAxi
    |G x p HSeq IH
    |G x y p HScope HSeq IH].
  - apply HIncl.
  - intros u HFree. right. apply IH, HFree.
  - apply IH.
  - simpl. apply incl_app.
    + assert (CtxVal (G;p)) as HVal. { apply validContext with q, HSeq. }
      apply validInScopeP, HVal.
    + apply IH.
  - apply incl_tran with (Fr (p :-> q)). 2: apply IH2.
    simpl. apply incl_appr, incl_refl.
  - rewrite <- free_not. apply validInScopeP, validContext with bot, HSeq.
  - rewrite axiomsClosed. 2: apply HAxi.
    apply incl_nil_l.
  - intros u HFree. simpl in HFree. rewrite remove_charac in HFree.
    destruct HFree as [HFree HNeq].
    simpl in IH. apply IH in HFree. destruct HFree as [Hu|Hu].
    + contradiction.
    + apply Hu.
  - rewrite free_permute.
    intros u HFree. apply in_map_iff in HFree.
    destruct HFree as [u' [H1 H2]].
    destruct (eqDec u' x) as [HEq|HxNeq].
      + subst. rewrite permute_app_right. left. reflexivity.
      + destruct (eqDec u' y) as [HEq|HyNeq].
        * subst. assert (y :: Fr' G). 2: contradiction.
          apply IH. simpl. apply remove_charac. split.
            { apply H2. }
            { intros HxEq. symmetry in HxEq. contradiction. }
        * rewrite permute_app_diff in H1.
            { subst. right. apply IH. simpl. apply remove_charac. split.
                { apply H2. }
                { intros HxEq. symmetry in HxEq. contradiction. }}
            { apply HyNeq. }
            { apply HxNeq. }
Qed.

Definition extract (v:Type) (e:Eq v) (G:Ctx v) (p:P v)
  : CtxVal G -> Fr p <= Fr' G -> G;p :- p := Extract G p.

Arguments extract {v} {e} {G} {p}.

Definition weakenV (v:Type) (e:Eq v) (G:Ctx v) (x:v) (p:P v)
  : ~(x :: Fr' G) -> G :- p -> G,x :- p := WeakenV G x p.

Arguments weakenV {v} {e} {G} {x} {p}.

Definition weakenP (v:Type) (e:Eq v) (G:Ctx v) (p q:P v)
  : Fr q <= Fr' G -> G :- p -> G;q :- p := WeakenP G p q.

Arguments weakenP {v} {e} {G} {p} {q}.

Definition deduct (v:Type) (e:Eq v) (G:Ctx v) (p q:P v)
  : G;p :- q -> G :- p :-> q := Deduct G p q.

Arguments deduct {v} {e} {G} {p} {q}.

Definition modus (v:Type) (e:Eq v) (G:Ctx v) (p q:P v)
  : G :- p -> G :- p :-> q -> G :- q := Modus G p q.

Arguments modus {v} {e} {G} {p} {q}.

Definition reduct (v:Type) (e:Eq v) (G:Ctx v) (p:P v)
  : G;¬p :- bot -> G :- p := Reduct G p.

Arguments reduct {v} {e} {G} {p}.

Definition axiomP (v:Type) (e:Eq v) (G:Ctx v) (p:P v)
  : CtxVal G -> IsAxiom p -> G :- p := AxiomP G p.

Arguments axiomP {v} {e} {G} {p}.

Definition general (v:Type) (e:Eq v) (G:Ctx v) (x:v) (p:P v)
  : G,x :- p -> G :- (All x p) := General G x p.

Arguments general {v} {e} {G} {x} {p}.

Definition special (v:Type) (e:Eq v) (G:Ctx v) (x y:v) (p:P v)
  : ~(y :: Fr' G)           ->        (* y not already in scope                 *)
    G   :- All x p          ->
    G,y :- fmap (y <:> x) p
  := Special G x y p.

(* Bot elimination:                                                             *)
(* Given a proof of the absurd, builds a proof of anything, provided the free   *)
(* variables are in scope. Note that contrary to propositional logic, we cannot *)
(* deduce just anything from the absurd, we cannot prove a proposition which is *)
(* nonesensical, i.e. whose free variables are not in scope of the context G    *)
(* The proof goes as follows:                                                   *)
(* G    :- bot                     : assumption                                 *)
(* G;¬p :- bot                     : weakening, ok if free vars in scope        *)
(* G    :- p                       : reduction                                  *)
Definition botElim (v:Type) (e:Eq v) (G:Ctx v) (p:P v)
  (HScope:Fr p <= Fr' G) (pr:G :- bot) : G :- p.
Proof.

  (* Leaving a hole for the proof that free vars are in scope *)
  refine (
    (reduct                         (* G    :- p              *)
      (weakenP _ pr))).             (* G;¬p :- bot            *)

  (* It remains to show that the free variables of ¬p are in scope *)
  assert (Fr (¬p) <= Fr' G) as A. 2: apply A.

  (* Since Fr (¬p) = Fr p ... *)
  rewrite free_not.

  (* Tt remains to show that the free variables of p are in scope *)
  assert (Fr p <= Fr' G) as A. 2: apply A.

  (* Which is true by our assumption HScope *)
  apply HScope.

Defined.

Arguments botElim {v} {e} {G} {p}.

(* And introduction:                                                            *)
(* Given proofs of G :- p and G :- q, builds a proof of G :- and p q            *)
(* The proof goes as follows:                                                   *)
(* G       :- p                    : (1) assumption                             *)
(* G       :- q                    : (2) assumption                             *)
(* G;p->¬q :- p                    : (3) weakening of (1)                       *)
(* G;p->¬q :- q                    : (4) weakening of (2)                       *)
(* G;p->¬q :- p -> ¬q              : (5) extraction                             *)
(* G;p->¬q :- ¬q                   : (6) modus ponens (3) and (5)               *)
(* G;p->¬q :- bot                  : (7) modus ponens (4) amd (6)               *)
(* G       :- ¬(p -> ¬q)           : deduction                                  *)
(* G       :- and p q              : and p q = ¬(p -> ¬q)                       *)
Definition andIntro (v:Type) (e:Eq v) (G:Ctx v) (p q:P v)
  (pr1:G :- p) (pr2:G :- q) : G :- and p q.
Proof.
  (* We shall need to prove that G is a valid context *)
  assert (CtxVal G) as HVal.
    (* Which follows from the fact the sequent G :- p as a proof pr1 *)
    { apply validContext with p, pr1. }

  (* We shall also need to prove that all free vars of p -> ¬q are in scope *)
  assert (Fr (p :-> ¬q) <= Fr' G) as HScope.
    { (* Expanding the lhs and using the fact that Fr q ++ [] = Fr q *)
      simpl. rewrite app_nil_r.

      (* We simply need to show that all free vars of p and q are in scope *)
      assert (Fr p ++ Fr q <= Fr' G) as A. 2: apply A.

      (* It is sufficient to deal with p and q separately *)
      apply incl_app.

          (* First we need to show the free vars of p are in scope *)
        - assert (Fr p <= Fr' G) as A. 2: apply A.

          (* Which follows from the fact the sequent G :- p has a proof pr1 *)
          apply freeVarsInScope, pr1.

          (* Next we need to show the free vars of q are in scope *)
        - assert (Fr q <= Fr' G) as A. 2: apply A.

          (* Which follows from the fact the sequent G :- q has a proof pr2 *)
          apply freeVarsInScope, pr2. }

  (* Leaving holes for the various proofs that need to be provided *)
  refine
    (deduct                              (* G       :- ¬(p -> ¬q)  *)
      (modus                             (* G;p->¬q :- bot         *)
        (weakenP _ pr2)                  (* G;p->¬q :- q           *)
        (modus                           (* G;p->¬q :- ¬q          *)
          (weakenP _ pr1)                (* G;p->¬q :- p           *)
          (extract _ _)))).              (* G;p->¬q :- p -> ¬q     *)

  (* Filling the holes with the required proofs *)
  - apply HScope.
  - apply HScope.
  - apply HVal.
  - apply HScope.
Defined.

Arguments andIntro {v} {e} {G} {p} {q}.

(* And left elimination:                                                        *)
(* Given a proof of G :- and p q, builds a proof of G :- p                      *)
(* The proof goes as follows:                                                   *)
(* G      :- and p q              : (1)  assumption                             *)
(* G      :- (p -> ¬q) -> bot     : (2)  and p q = ¬(p -> ¬q)                   *)
(* G;¬p   :- (p -> ¬q) -> bot     : (3)  weakening of (2)                       *)
(* G;¬p   :- ¬p                   : (4)  extraction                             *)
(* G;¬p;p :- p                    : (5)  extraction                             *)
(* G;¬p;p :- ¬p                   : (6)  weakening of (4)                       *)
(* G;¬p;p :- bot                  : (7)  modus ponens of (5) and (6)            *)
(* G;¬p;p :- ¬q                   : (8)  bot elimination in (7)                 *)
(* G;¬p   :- p -> ¬q              : (9)  deduction from (8)                     *)
(* G;¬p   :- bot                  : (10) modus ponens of (3) and (9)            *)
(* G      :- p                    : (11) reduction                              *)
Definition andElimL (v:Type) (e:Eq v) (G:Ctx v) (p q:P v) (pr:G :- and p q) : G :- p.
Proof.
  (* We shall need to prove that G is a valid context *)
  assert (CtxVal G) as HVal. { apply validContext with (and p q), pr. }

  (* We shall also need to prove that all free vars of p are in scope *)
  assert (Fr p <= Fr' G) as HpScope. {

    (* From the sequent G :- and p q, all free vars of and p q are in scope *)
    assert (Fr (and p q) <= Fr' G) as Hpq. { apply freeVarsInScope, pr. }

    (* Using transitivity of inclusion *)
    apply incl_tran with (Fr (and p q)). 2: apply Hpq.

    (* It is sufficient to prove that Fr p <= Fr (and p q) *)
    assert (Fr p <= Fr (and p q)) as A. 2: apply A.

    (* After simplification of the rhs *)
    simpl. rewrite app_nil_r, app_nil_r.

    (* We need to show that Fr p <= Fr p ++ Fr q *)
    assert (Fr p <= Fr p ++ Fr q) as A. 2: apply A.

    (* Which is clear *)
    apply incl_appl, incl_refl.

  }

  (* And all free vars of q are in scope *)
  assert (Fr q <= Fr' G) as HqScope. {

    (* From the sequent G :- and p q, all free vars of and p q are in scope *)
    assert (Fr (and p q) <= Fr' G) as Hpq. { apply freeVarsInScope, pr. }

    (* Using transitivity of inclusion *)
    apply incl_tran with (Fr (and p q)). 2: apply Hpq.

    (* It is sufficient to prove that Fr q <= Fr (and p q) *)
    assert (Fr q <= Fr (and p q)) as A. 2: apply A.

    (* After simplification of the rhs *)
    simpl. rewrite app_nil_r, app_nil_r.

    (* We need to show that Fr q <= Fr p ++ Fr q *)
    assert (Fr q <= Fr p ++ Fr q) as A. 2: apply A.

    (* Which is clear *)
    apply incl_appr, incl_refl.
  }

  (* Leaving holes for the various proofs that need to be provided      *)
  refine (reduct                          (* G      :- p                *)
            (modus                        (* G;¬p   :- bot              *)
              (deduct                     (* G;¬p   :- p -> ¬q          *)
                (botElim _                (* G;¬p;p :- ¬q               *)
                  (modus                  (* G;¬p;p :- bot              *)
                    (extract _ _)         (* G;¬p;p :- p                *)
                    (weakenP _            (* G;¬p;p :- ¬p               *)
                      (extract _ _)))))   (* G;¬p   :- ¬p               *)
              (weakenP _ pr))).           (* G;¬p   :- (p -> ¬q) -> bot *)

  (* Filling the holes with the required proofs *)
  - rewrite free_not. apply HqScope.
  - constructor. 2: apply HVal. rewrite free_not. apply HpScope.
  - apply HpScope.
  - apply HpScope.
  - apply HVal.
  - rewrite free_not. apply HpScope.
  - rewrite free_not. apply HpScope.

Defined.

Arguments andElimL {v} {e} {G} {p} {q}.

