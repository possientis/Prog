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
    CtxVal G              ->
    Fr (All x p) <= Fr' G ->
    ~ (y :: Fr' G)        ->
    Seq v e (G;All x p,y) (fmap (y <:> x) p)
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
    |G x p HScope HSec IH
    |G p q HIncl  HSec IH
    |G p q HSeq IH
    |G p q HSeq1 IH1 ISeq2 IH2
    |G p HSeq IH
    |G p HVal HAxi
    |G x p HSeq IH
    |G x y p HVal HIncl HScope].
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
      + constructor.
        * apply HIncl.
        * apply HVal.
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
    |G x p HScope HSec IH
    |G p q HIncl  HSec IH
    |G p q HSeq IH
    |G p q HSeq1 IH1 ISeq2 IH2
    |G p HSeq IH
    |G p HVal HAxi
    |G x p HSeq IH
    |G x y p HVal HIncl HScope].
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
        apply HIncl. simpl. apply remove_charac. split.
          { apply H2. }
          { intros HxyEq. apply HxNeq. symmetry. apply HxyEq. }
      * rewrite permute_app_diff in H1.
          { subst. right. apply HIncl. simpl. apply remove_charac. split.
            { apply H2. }
            { intros HxuEq. apply HxNeq. symmetry. apply HxuEq. }}
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
  : CtxVal G              ->          (* context is valid                       *)
    Fr (All x p) <= Fr' G ->          (* all free vars of 'All x p' in scope    *)
    ~(y :: Fr' G)         ->          (* y not already in scope                 *)
    G;All x p,y :- fmap (y <:> x) p
  := Special G x y p.

(* Bot elimination:                                                             *)
(* Given a proof of the absurd, builds a proof of anything, provided the free   *)
(* variables are in scope. Note that contrary to propositional logic, we cannot *)
(* deduce just anything from the absurd, we cannot prove a proposition which is *)
(* nonesensical, i.e. whose free variables are not in scope of the context G    *)
(* The proof goes as follows:                                                   *)
(* G    :- bot                     ; assumption                                 *)
(* G;¬p :- bot                     : weakening, ok if free vars in scope        *)
(* G    :- p                       : reduction                                  *)
Definition botElim (v:Type) (e:Eq v) (G:Ctx v) (p:P v) (pr:G :- bot)
  : Fr p <= Fr' G -> G :- p.
Proof.

  (* Leaving a hole for the proof that free vars are in scope *)
  refine (fun (HScope : Fr p <= Fr' G) => reduct (weakenP _ pr)).

  (* It remains to show that the free variables of ¬p are in scope *)
  assert (Fr (¬p) <= Fr' G) as A. 2: apply A.

  (* Since Fr (¬p) = Fr p ... *)
  rewrite free_not.

  (* Tt remains to show that the free variables of p are in scope *)
  assert (Fr p <= Fr' G) as A. 2: apply A.

  (* Which is true by our assumption HScope *)
  apply HScope.

Defined.
