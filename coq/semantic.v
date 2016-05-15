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
  P s -> exec s (WhileDo b i) s' -> 
  P s' /\ evalB s' b = Some false.
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

Theorem InfiniteLoop : forall (s1 s2:state)(b:bExp), 
  evalB s1 b = Some true -> ~ exec s1 (WhileDo b Skip) s2.





