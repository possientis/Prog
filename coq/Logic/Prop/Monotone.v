Require Import Logic.List.In.
Require Import Logic.List.Include.

Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Proof.

(* A proposition which belongs to a context is provable from that context       *)
(* Note that the assumption p :: G allows us to show the existence of a proof   *)
(* for the sequent G :- p, i.e. we can show G ;- p. However, this assumption is *)
(* not enough to create a proof term, as it depends on the position of p in G   *)
Lemma inCtx : forall (v:Type) (G:Ctx v) (p:P v), p :: G -> G ;- p.
Proof.

  (* Let v be a type and G be a context in v *)
  intros v G.

  (* Let p be a propositional formula with atoms in v *)
  intros p.

  (* We need to show the implication p :: G -> G ;- p *)
  assert (p :: G -> G ;- p) as A. 2: apply A.

  (* We do so by induction on the context G *)
  induction G as [|q G' IH].

    (* First we assume that G is the empty context: implication vacuously true *)
    - intros H. inversion H.

    (* Next we assume that G = G';q, so we assume that p :: G';q *)
    - intros H. assert (p :: G';q) as A. apply H. clear A.

      (* We need to show G';q ;- p *)
      assert (G';q ;- p) as A. 2: apply A.

      (* We shall distinguish two cases *)
      destruct H as [H|H].

        (* First we assume that q = p, then the proof exists by hypothesis *)
        + rewrite H. exists fromHyp. apply I.

        (* Next we assume that p lies in G', then use induction hypothesis *)
        + destruct (IH H) as [e _]. exists (weaken e). apply I.
Qed.

(* Suppose G H are contexts such that every element of G is provable under H    *)
(* Then any proposition provable under G is also provable under H               *)
Lemma compose : forall (v:Type) (G H:Ctx v),
  (forall (p:P v), p :: G -> H ;- p) -> forall (p:P v), G ;- p -> H ;- p.
Proof.
  (* Let v be a type and G H be contexts in v *)
  intros v G H.

  (* We assume that any element of G is provable under H *)
  intros GH.
  assert (forall (p:P v), p :: G -> H ;- p) as A. apply GH. clear A.

  (* Let p be a proposition with atoms in v *)
  intros p.

  (* We assume we have e :: G :- p *)
  intros [e _].

  (* We need to show that p is provable under H *)
  assert (H ;- p) as A. 2: apply A.

  (* Let us revert the assumption GH *)
  revert GH. revert H.

  (* Then we need to show that given the proof e: G :-p, for all context H with *)
  (* property GH, p is provable under H. We proceed by induction e              *)
  induction e as
    [G p|G p q e IH|G p q e IH|G p q e1 IH1 e2 IH2|G p e IH]; intros H GH.

    - apply GH. left. reflexivity.
    - apply IH. intros r Hr. apply GH. right. apply Hr.
    - assert (H;p ;- q) as K.
        { apply IH. intros r Hr. destruct Hr as [Hr|Hr].
            - rewrite Hr. exists fromHyp. apply I.
            - destruct (GH r Hr) as [e' _]. exists (weaken e'). apply I. }
      destruct K as [e' _]. exists (deduct e'). apply I.
    - destruct (IH1 H GH) as [e1' _]. destruct (IH2 H GH) as [e2' _].
      exists (modus e1' e2'). apply I.
    - assert (H;¬p ;- bot) as K.
        { apply IH. intros r Hr. destruct Hr as [Hr|Hr].
          - rewrite Hr. exists fromHyp. apply I.
          - destruct (GH r Hr) as [e' _]. exists (weaken e'). apply I. }
      destruct K as [e' _]. exists (reduct e'). apply I.
Qed.

(* A provable proposition is provable under a larger context                    *)
Lemma monotone : forall (v:Type) (G H:Ctx v) (p:P v), G <= H -> G ;- p  -> H ;- p.
Proof.
  (* Let v be a type and G H be context in v *)
  intros v G H.

  (* Let p be a formula of propositional logic with atoms in v *)
  intros p.

  (* We assume that H is a larger context than G *)
  intros HLeq. assert (G <= H) as A. apply HLeq. clear A.

  (* We assume we have a proof e : G :- p *)
  intros [e _].

  (* We need to show that p is provable under H *)
  assert (H ;- p) as A. 2: apply A.

  (* We apply the compose lemma *)
  apply compose with G. 2: { exists e.  apply I. }

  (* We simply need to show that every element of G is provable under H *)
  assert (forall (q:P v), q :: G -> H ;- q) as A. 2: apply A.

  (* So let q be a proposition *)
  intros q.

  (* We assume that q lies in G *)
  intros Hq. assert (q :: G) as A. apply Hq. clear A.

  (* We need to show that q is provable under H *)
  assert (H ;- q) as A. 2: apply A.

  (* We apply lemme inCtx *)
  apply inCtx.

  (* It remains to show that q lies in H *)
  assert (q :: H) as A. 2: apply A.

  (* This follows immediately from the assumption G <= H *)
  apply HLeq, Hq.
Qed.
