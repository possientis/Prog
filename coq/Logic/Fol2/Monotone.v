Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Permute.

Require Import Logic.List.In.
Require Import Logic.List.Include.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol2.Axiom.
Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Proof.

(*
(* A proposition which belongs to a valid context is provable from that context *)
(* Note that the assumption p :: G allows us to show the existence of a proof   *)
(* for the sequent G :- p, i.e. we can show G ;- p. However, this assumption is *)
(* not enough to create a proof term, as it depends on the position of p in G   *)
Lemma inCtx : forall (v:Type) (e:Eq v) (G:Ctx v) (p:P v),
    (CtxVal G)    ->    (* Context G is valid           *)
    (Prp p) :: G  ->    (* p is part of the context G   *)
    G ;- p.             (* p is provable from context G *)
Proof.

  (* Let v be a type, e a decidable equality on v and G be a context in v *)
  intros v e G.

  (* Let p be a proposition with variables in v *)
  intros p.

  (* We need to show the implication CtxVal G -> (Prp p) :: G -> G ;- p *)
  assert (CtxVal G -> Prp p :: G -> G ;- p) as A. 2: apply A.

  (* We do so by induction on the context G *)
  induction G as [|ent G' IH].

    (* First we assume that G is the empty context: implication vacuously true *)
    - intros _ H. inversion H.

    (* Next we assume that G = G';q or G = G',x: we consider both cases *)
    - destruct ent as [x|q].

      (* First we assume that G = G',x, that it is valid and (Prp p) :: G',x *)
      + intro HVal. assert (CtxVal (G',x)) as A. apply HVal. clear A.

        intro HIn. assert (Prp p :: G',x) as A. apply HIn. clear A.

        (* We need to show that G',x ;- p *)
        assert (G',x ;- p) as A. 2: apply A.

        (* G',x being valid, G' is itself valid *)
        assert (CtxVal G') as HVal'. { apply validInvertV with x, HVal. }

        (* From Prp p :: G',x we also have Prp p :: G' *)
        assert (Prp p :: G') as HIn'. { destruct HIn as [HIn|HIn].
          { inversion HIn. }
          { apply HIn. }
        }

        (* From our induction hypothesis, it follows that G' ;- p *)
        assert (G' ;- p) as HSeq. { apply IH.
          { apply HVal'. }
          { apply HIn'. }
        }

        (* let pr be a proof of G' :- p *)
        destruct HSeq as [pr _].

        (* Note that x is not already in scope G' *)
        assert (~ x :: Fr' G') as HScope. { apply validInScopeV, HVal. }

        (* Hence by weakening we obtain a proof of G',x :- p *)
        exists (weakenV HScope pr). apply I.

      (* Next we assume that G = G';q, that it is valid and (Prp p) :: G';q *)
      + intro HVal. assert (CtxVal (G';q)) as A. apply HVal. clear A.

        intro HIn. assert (Prp p :: G';q) as A. apply HIn. clear A.

        (* We need to show that G';q ;- p *)
        assert (G';q ;- p) as A. 2: apply A.

        (* G';q being valid, G' is itself valid *)
        assert (CtxVal G') as HVal'. { apply validInvertP with q, HVal. }

        (* Note that all free vars of q are in scope *)
        assert (Fr q <= Fr' G') as HScope. { apply validInScopeP, HVal. }

        (* We shall distinguish two cases *)
        destruct HIn as [HIn|HIn].

          (* First we assume that q = p *)
          * inversion HIn. subst. exists (extract HVal' HScope). apply I.

          (* Next we assume that q <> p, let pr be a proof of G' :- p *)
          * destruct (IH HVal' HIn) as [pr _].

            (* By weakening we obtain a proof of G';q :- p *)
            exists (weakenP HScope pr). apply I.
Qed.
*)
(* Suppose G H are contexts where every proposition of G is provable under H.   *)
(* Then any proposition provable under G is also provable under H.              *)
(* This is not quite true as stated. We need the context H to be valid. We also *)
(* need every variable which is in scope of G to be in scope of H, that is      *)
(* Fr' G <= Fr' H. Consider the case when G=x and H=nil. Then G has no prop     *)
(* and the proposition x <: x -> x <: x is provable under G but not under H.    *)
(* Note that assuming G to be valid is not required.                            *)
(* TODO: Find a way to prove this
Lemma compose : forall (v:Type) (e:Eq v) (G H:Ctx v),
  CtxVal H                                 -> (* H is a valid context           *)
  Fr' G <= Fr' H                           -> (* x in scope G -> x in scope H   *)
  (forall (p:P v), (Prp p) :: G -> H ;- p) -> (* Props in G are provable in H   *)
  forall (p:P v), G ;- p -> H ;- p.           (* G-provable -> H-provable       *)
Proof.
  (* Let v be a type, e be a decidable equality on v and G H be contexts in v   *)
  intros v e G H.

  (* We assume that H is a valid context *)
  intro HValH. assert (CtxVal H) as A. apply HValH. clear A.

  (* We assume that the scope of G is inside the scope of H *)
  intro HScope. assert (Fr' G <= Fr' H) as A. apply HScope. clear A.

  (* We assume that any proposition of G is provable under H *)
  intros GH.
  assert (forall (p:P v), Prp p :: G -> H ;- p) as A. apply GH. clear A.

  (* Let p be a proposition with variables in v *)
  intros p.

  (* We assume it is provable under G, so we have pr : G :- p *)
  intros [pr _].

  (* We need to show that p is provable under H *)
  assert (H ;- p) as A. 2: apply A.

  (* Let us revert all assumptions which involve H *)
  revert H HValH HScope GH.

  (* Then we need to show that given a proof pr:G :- p, for all valid context   *)
  (* H whose scope contains that of G and which satifies property GH, p is      *)
  (* provable under H. We proceed by structural induction on the proof pr       *)
  induction pr as
    [G p HVal HIncl
    |G x p HScope' HSeq IH
    |G p q HIncl  HSeq IH
    |G p q HSeq IH
    |G p q HSeq1 IH1 ISeq2 IH2
    |G p HSeq IH
    |G p HVal HAxi
    |G x p HSeq IH
    |G x y p HScope' HSeq IH]; intros H HValH HScope GH.

  - apply GH. left. reflexivity.

  - apply IH.
    + apply HValH.
    + intros u Hu. apply HScope. right. apply Hu.
    + intros q Hq. apply GH. right. apply Hq.

  - apply IH.
    + apply HValH.
    + apply HScope.
    + intros r Hr. apply GH. right. apply Hr.

  - assert (H;p ;- q) as K. {
      assert (Fr p <= Fr' G) as HpScope. {
        apply validInScopeP, validContext with q, HSeq.
      } (* HpScope: Fr p <= Fr' G *)
      apply IH.
      - constructor. 2: apply HValH. intros u Hu. apply HScope.
        apply HpScope, Hu.
      - apply HScope.
      - intros r Hr. destruct Hr as [Hr|Hr].
        + inversion Hr. subst.
          assert (Fr r <= Fr' H) as HrScope. {
            intros u Hu. apply HScope. apply validInScopeP with r.
            apply validContext with q, HSeq. apply Hu.
          } (* HrScope: Fr r <= Fr' H *)
          exists (extract HValH HrScope). apply I.
        + destruct (GH r Hr) as [pr _].
          assert (Fr p <= Fr' H) as HpScope'. {
            apply incl_tran with (Fr' G).
            - apply HpScope.
            - apply HScope.
          } (* HpScope': Fr p <= Fr' H *)
          exists (weakenP HpScope' pr). apply I.
    } (* K: H;p ;- q *)
    destruct K as [pr _]. exists (deduct pr). apply I.

  - destruct (IH1 H HValH HScope GH) as [pr1 _].
    destruct (IH2 H HValH HScope GH) as [pr2 _].
    exists (modus pr1 pr2). apply I.

  - assert (H;¬p ;- bot) as K. {
      assert (Fr p <= Fr' G) as HpScope. {
        rewrite <- free_not. apply validInScopeP, validContext with bot, HSeq.
      } (* HpScope: Fr p <= Fr' G *)
      apply IH.
      - constructor. 2: apply HValH. rewrite free_not.
        apply incl_tran with (Fr' G).
        + apply HpScope.
        + apply HScope.
      - apply HScope.
      - intros q Hq.
        assert (Fr (¬p) <= Fr' H) as HpScope'. {
          rewrite free_not. apply incl_tran with (Fr' G).
          - apply HpScope.
          - apply HScope.
        } (* HpScope': Fr (¬p) <= Fr' H *)
        destruct Hq as [Hq|Hq].
        + inversion Hq.
         exists (extract HValH HpScope'). apply I.
        + destruct (GH q Hq) as [pr _]. exists (weakenP HpScope' pr). apply I.
    } (* K: H;¬p :- bot *)
    destruct K as [pr _]. exists (reduct pr). apply I.

  - exists (axiomP HValH HAxi). apply I.

  - assert (H,x ;- p) as K. {
      apply IH.

Show.
*)
