Require Import Bool.
Require Import Logic.List.In.

Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Semantics.

Declare Scope Prop_Entails_scope.

(* Semantic entailment: G ::- p holds if and only if for all truth assignment   *)
(* f: v -> bool, if every q in the context G is true (relative to f), then p is *)
(* also true (relative to f)                                                    *)
Definition Entails (v:Type)(G:Ctx v) (p:P v) : Prop :=
  forall (f:v -> bool),
  (forall (q:P v), (q :: G) -> eval f q = true) -> eval f p = true.

Arguments Entails {v}.

Notation "G ::- p" := (Entails G p)
  (at level 90, no associativity) : Prop_Entails_scope.

Open Scope Prop_Entails_scope.

(* Semantic from hypothesis rule                                                *)
Lemma entFromHyp : forall (v:Type) (G:Ctx v) (p:P v),
  G;p ::- p.
Proof.
  intros v G p f H. apply H. left. reflexivity.
Qed.

(* Semantic weakening rule                                                      *)
Lemma entWeaken : forall (v:Type) (G:Ctx v) (p q:P v),
  G ::- p -> G;q ::- p.
Proof.
  intros v G p q H1 f H2. apply H1. intros r H3. apply H2. right. apply H3.
Qed.

(* Semantic deduction rule                                                      *)
Lemma entDeduct : forall (v:Type) (G:Ctx v) (p q:P v),
  G;p ::- q -> G ::- p :-> q.
Proof.
  (* Let v be a type and G be a context on v  *)
  intros v G.

  (* Let p q be two formulas of propositional logic *)
  intros p q.

  (* We assume that the semantic entailment G,p ::- q holds *)
  intros HEntails. assert (G;p ::- q) as A. apply HEntails. clear A.

  (* We need to show rhar G ::- p :-> q *)
  assert (G ::- p :-> q) as A. 2: apply A.

  (* Let f:v -> bool be a truth assignment *)
  intro f.

  (* We assume every element of G is satisfied by the associated semantics *)
  intros HSat.
  assert (forall (r:P v), r :: G -> eval f r = true) as A. apply HSat. clear A.

  (* We need to show that p :-> q is true under this semantics  *)
  assert (eval f (p :-> q) = true) as A. 2: apply A.

  (* Define x = eval f p *)
  remember (eval f p) as x eqn:E.

  (* We distinguish two cases depending on whether x is true or not *)
  destruct x.

    (* Case when eval f p = true *)
    - simpl. apply orb_true_intro. right.

      (* We need to show that q is true *)
      assert (eval f q = true) as A. 2: apply A.

      (*  We apply are assumption G;p ::- q *)
      apply HEntails.

      (* So we need to prove all propositions of G;p are true *)
      assert (forall (r:P v), r :: G;p -> eval f r = true) as A. 2: apply A.

      (* So let r be a proposition of context G;p *)
      intros r [H1|H1].

        (* We assume that r = p *)
        + rewrite <- H1, E. reflexivity.

        (* We assume that r is in G *)
        +  apply HSat, H1.

    (* Case when eval f p = false *)
    - simpl. apply orb_true_intro. left. rewrite <- E. reflexivity.
Qed.

(* Semantic modus ponens rule                                                   *)
Lemma entModus : forall (v:Type) (G:Ctx v) (p q: P v),
  G ::- p -> G ::- (p :-> q) -> G ::- q.
Proof.
  (* Let v be a type and G be a context on v *)
  intros v G.

  (* Let p q be formulas of propositional logic with atoms in v *)
  intros p q.

  (* We assume that G ::- p holds *)
  intros Hp. assert (G ::- p) as A. apply Hp. clear A.

  (* We assume that G ::- p :-> q holds *)
  intros Hpq. assert (G ::- p :-> q) as A. apply Hpq. clear A.

  (* We need to show that G ::- q *)
  assert (G ::- q) as A. 2: apply A.

  (* So let f:v -> bool be a truth assignment *)
  intro f.

  (* for which every formula in G is true *)
  intro HSat.
  assert (forall (r:P v), r :: G -> eval f r = true) as A.
  apply HSat. clear A.

  (* We need to to show that q is also true *)
  assert (eval f q = true) as A. 2: apply A.

  (* However p is true *)
  assert (eval f p = true) as Ep. { apply Hp, HSat. }

  (* and p :-> q is alsu true *)
  assert (eval f (p :-> q) = true) as Epq. { apply Hpq, HSat. }

  (* So we can now conclude *)
  simpl in Epq. apply orb_prop in Epq. destruct Epq as [H|H].

    (* case p is false leads to a contradiction *)
    - rewrite Ep in H. simpl in H. inversion H.

    (* case q is true gives the desired conclusion *)
    - apply H.
Qed.

(* Semantic reductio ad absurdum rule                                           *)
Lemma entReduct : forall (v:Type) (G:Ctx v) (p: P v),
  G;¬p ::- bot -> G ::- p.
Proof.
  (* Let v be a type and G be a context in v *)
  intros v G.

  (* Let p be a formula of propositional logic with atoms in v *)
  intro p.

  (* We assume that G;¬p ::- bot holds *)
  intro HEntails. assert (G;¬p ::- bot) as A. apply HEntails. clear A.

  (* We need to show that G ::- p holds *)
  assert (G ::- p) as A. 2: apply A.

  (* So let f:v -> bool be a trith assignment *)
  intro f.

  (* for which all formulas in G are true *)
  intro HSat.
  assert (forall (q:P v), q :: G -> eval f q = true) as A.
  apply HSat. clear A.

  (* We need to show that p is true *)
  assert (eval f p = true) as A. 2: apply A.

  (* Let x = eval f p *)
  remember (eval f p) as x eqn:E.

  (* We consider the two possible cases for x *)
  destruct x.

    (* First we assume that x = true, there os nothing to prove *)
    - reflexivity.

    (* Next we assume that x = false, we need to obtain a contradiction *)
    - exfalso.

      (* This will be our contradiction *)
      assert (eval f bot = true) as C.
        { (* We need to show that bot is true *)
          assert (eval f bot = true) as A. 2: apply A.

          (* Using our assumption G;¬p :- bot *)
          apply HEntails.

          (* We need to show all q's in G;¬p are true *)
          assert (forall (q:P v), q :: G;¬p -> eval f q = true) as A. 2: apply A.

          (* So let q be a formula with atoms in v *)
          intro q.

          (* Assume that g lies in g;¬p *)
          intro Hq. assert (q :: G;¬p) as A. apply Hq. clear A.

          (* We need to show that q is true *)
          assert (eval f q = true) as A. 2: apply A.

          (* We consider two cases *)
          destruct Hq as [Hq|Hq].

            (* First we assume that q = ¬p *)
            - rewrite <- Hq. simpl. apply orb_true_intro. left.
              rewrite <- E. reflexivity.

            (* Next we assume that q lies in G *)
            - apply HSat, Hq. }

      (* We now have a contradiction *)
      inversion C.
Qed.
