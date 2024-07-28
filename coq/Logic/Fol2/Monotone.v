Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Include.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Proof.

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


