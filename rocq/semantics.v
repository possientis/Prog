(* the two fundamental rules of the 'elim' tactic:
  1. Always keep the relevant assumptions in the goal (use 'generalize' if needed)
  2. The arguments of an inductive predicate on which you call 'elim' should be variables (use 'set v:= ..' if needed)
*)

Require Import ZArith.

Parameters Var aExp bExp : Set.

Inductive inst : Set :=
  | Skip      : inst
  | Assign    : Var -> aExp -> inst
  | Sequence  : inst -> inst -> inst
  | WhileDo   : bExp -> inst -> inst.

Parameters
  (state  : Set)
  (update : state -> Var -> Z -> option state)
  (evalA  : state -> aExp -> option Z)
  (evalB  : state -> bExp -> option bool). 


Inductive exec : state -> inst -> state -> Prop :=

  | execSkip        : forall s:state, exec s Skip s

  | execAssign      : forall (s s1:state)(v:Var)(n:Z)(a:aExp),
                      evalA s a = Some n -> update s v n = Some s1 -> 
                      exec s (Assign v a) s1

  | execSequence    : forall (s s1 s2:state)(i1 i2:inst),
                      exec s i1 s1 -> exec s1 i2 s2 -> 
                      exec s (Sequence i1 i2) s2

  | execWhileFalse  : forall (s:state)(i:inst)(e:bExp),
                      evalB s e = Some false -> exec s (WhileDo e i) s

  | execWhileTrue   : forall (s s1 s2:state)(i: inst)(e:bExp),
                      evalB s e = Some true -> exec s i s1 ->
                      exec s1 (WhileDo e i) s2 ->
                      exec s (WhileDo e i) s2. 

Theorem HoareWhileRule :
  forall (P:state -> Prop)(b:bExp)(i:inst)(s s':state),
  (forall (s1 s2:state), 
  P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2) ->
  P s -> exec s (WhileDo b i) s' -> P s' /\ evalB s' b = Some false.
Proof.
  intros P b i s s' H.
  cut (forall j:inst, exec s j s' -> j = WhileDo b i -> 
    P s -> P s'/\ evalB s' b = Some false).
  eauto. (* quite handy after a 'cut' *)
  (* clever trick 'elim ... ; try (intros; discriminate) *)
  intros j Hex. elim Hex; try (intros; discriminate).
  intros s0 i0 e Hev Heq. injection Heq; intros H1 H2. (* do not forget injection *)
  (* not very useful here but to be remembered *)
  match goal with
    | [id:(e = b) |- _ ]  => rewrite <- id
  end.
  auto.

  intros.
  match goal with
    | [id:(_ = _) |- _] => injection id; intros H' H''
  end.
  apply H4. exact H5. apply H with (s1:=s0). exact H6.
  rewrite <- H''. exact H0. rewrite <- H'. exact H1.
Qed.

Lemma SkipNoChange: forall (s1 s2:state),
  exec s1 Skip s2 -> s1 = s2.
Proof.
  cut (forall (s1 s2:state)(i:inst), i = Skip -> exec s1 i s2 -> s1 = s2).
  eauto. intros s1 s2 i Hi Hex. generalize Hex Hi. clear Hi.
  elim Hex; try (intros; discriminate). auto.
Qed.
  

Theorem InfiniteLoop : forall (s1 s2:state)(b:bExp), 
  evalB s1 b = Some true -> ~ exec s1 (WhileDo b Skip) s2.
Proof.
  cut (forall (s1 s2:state)(b:bExp)(i:inst),
    i = WhileDo b Skip -> evalB s1 b = Some true -> ~ exec s1 i s2).
  eauto. (* eauto trick after a 'cut' which is close enough to goal *)
  intros s1 s2 b i Hi Hb Hex. generalize Hex Hb Hi. clear Hi Hb. generalize b.
  elim Hex; try (intros; discriminate). (* trick *)
  intros. injection Hi. intros. rewrite H1 in H. rewrite H in Hb.
  discriminate Hb. intros. injection Hi. intros. clear Hi b.
  rewrite H4 in H0. rewrite H4 in H1. rewrite H4 in H2. rewrite H4 in H3.
  rewrite <- H5 in Hb. rewrite H4 in Hex0. clear H4 H5 Hb. clear H1.
  apply H3 with (b:=e). exact H2. cut (s0 = s). intro Hs. rewrite Hs. exact H.
  symmetry. apply SkipNoChange. exact H0. reflexivity.
Qed.

Theorem HoareSequenceRule:
  forall (P:state -> Prop)(i1 i2:inst)(s s': state),
  (forall (s1 s2: state), P s1 -> exec s1 i1 s2 -> P s2) ->
  (forall (s2 s3: state), P s2 -> exec s2 i2 s3 -> P s3) ->
  P s -> exec s (Sequence i1 i2) s' -> P s'.
Proof.
  intros P i1 i2 s s' H1 H2. 
  cut (forall i:inst, 
    P s -> i = (Sequence i1 i2) -> exec s i s' -> P s'). 
  eauto. (* eauto trick after a cut *) 
  intros i Hs Hi Hex. generalize Hex Hi Hs H1 H2. clear H1 H2 Hi Hs.
  generalize i1 i2 P. clear i1 i2 P. elim Hex; try (intros; discriminate). (* trick *)
  clear s s' i Hex. intros s1 s2 s3 i1 i2 H1 H1' H2 H2' i0 i3 P H12 H0 Hs1 I1 I2.
  injection H0. intros E2 E1. clear H0. rewrite <- E1 in I1. rewrite <- E2 in I2.
  clear E1 E2 H1' H2'. apply (I2 s2 s3). apply (I1 s1 s2). 
  exact Hs1. exact H1. exact H2.
Qed.


