Require Import Logic.Class.Eq.

Require Import Logic.STLC.Syntax.

Inductive Binding (b v:Type) : Type :=
| BType : b -> Binding b v          (* Adding base type to context              *)
| BVar  : v -> T b -> Binding b v   (* Adding variable to context               *)
.

Arguments Binding {b} {v}.
Arguments BType   {b} {v}.
Arguments BVar    {b} {v}.

Notation "Ty ::: *" := (BType Ty)
    (at level 1, no associativity)      : STLC_Context_scope.

Notation "x ::: Ty" :=(BVar x Ty)
    (at level 1, no associativity)      : STLC_Context_scope.


Inductive Context (b v:Type) : Type :=
| O         : Context b v
| CtxSnoc   : Context b v -> @Binding b v -> Context b v
.

Arguments Context {b} {v}.
Arguments O       {b} {v}.
Arguments CtxSnoc {b} {v}.

Notation "G ; x" := (CtxSnoc G x)
    (at level 50, left associativity) : STLC_Context_scope.

Open Scope STLC_Context_scope.

Inductive FindTy (b v:Type) : @Context b v -> b -> Prop :=
| FindTyZ : forall (G:Context) (t:b), FindTy b v (G ; t ::: *) t
| FindTyS : forall (G:Context) (t:b) (k:Binding),
    FindTy b v G t -> FindTy b v (G ; k) t
.

Arguments FindTy  {b} {v}.
Arguments FindTyZ {b} {v}.
Arguments FindTyS {b} {v}.

Notation "G :> Ty" := (FindTy G Ty)
    (at level 60, no associativity) : STLC_Context_scope.

Lemma findTyRev : forall (b v:Type) (G:Context) (x:v) (Ty:T b) (t : b),
    G ; x ::: Ty :> t -> G :> t.
Proof.
    intros b v G x Ty t H1. remember (G ; x ::: Ty) as G' eqn:E.
    revert G x Ty E. destruct H1 as [G t|G t k H1]; intros G' x Ty H2.
    - inversion H2. 
    - inversion H2. subst. assumption.
Qed.

Lemma findTyRev' : forall (b v:Type) (G:@Context b v) (t t':b),
    G ; t ::: * :> t' -> t = t' \/ G :> t'.
Proof.
    intros b v G t t' H1. remember (G;t ::: *) as G' eqn:E.
    revert G t E. destruct H1 as [G t|G t k H2];
    intros G' t' H3; inversion H3. 
    - left. reflexivity.
    - subst. right. assumption.
Qed.

Inductive FindVar (b v:Type) (e:Eq v) : @Context b v -> @Binding b v -> Prop :=
| FindVarZ : forall (G:Context) (x:v) (Ty:T b), 
    FindVar b v e (G ; x ::: Ty) (x ::: Ty)
| FindVarSkip : forall (G:Context) (k:Binding) (t:b),
    FindVar b v e G k -> FindVar b v e (G ; t ::: * ) k
| FindVarS : forall (G:Context) (x y:v) (Ty Ty':T b),
    x <> y                                      ->
    FindVar b v e G (x ::: Ty)                  ->
    FindVar b v e (G ; y ::: Ty') (x ::: Ty)
.

Arguments FindVar     {b} {v} {e}.
Arguments FindVarZ    {b} {v} {e}.
Arguments FindVarSkip {b} {v} {e}.
Arguments FindVarS    {b} {v} {e}.

Notation "G :>> k" := (FindVar G k)
    (at level 60, no associativity) : STLC_Context_scope.

Lemma findVarRev : forall (b v:Type) (e:Eq v) (G:Context) (t:b) (x:v) (Ty:T b),
    G ; t ::: * :>> x ::: Ty -> G :>> x ::: Ty.
Proof.
    intros b v e G t x Ty H1.
    remember (G ; t ::: *) as G' eqn:E. remember (x ::: Ty) as k eqn:F.
    revert G t x Ty E F. destruct H1 as [G x Ty|G k Ty H1|G x y Ty Ty' H1 H2];
    intros G' t x' Sy H3 H4. 
    - inversion H3.
    - inversion H3. subst. assumption.
    - inversion H3.
Qed.

Definition ctxIncl (b v:Type)(e:Eq v)(G H:@Context b v) : Prop :=
    (forall (t:b), G :> t -> H :> t) /\
    (forall (x:v) (Ty:T b), G :>> x ::: Ty -> H :>> x ::: Ty).

Arguments ctxIncl {b} {v} {e}.

Notation "G <= H"  := (ctxIncl G H)
    (at level 70, no associativity) : STLC_Context_scope.

Open Scope STLC_Context_scope.

Lemma ctxInclO : forall (b v:Type) (e:Eq v) (G:@Context b v), 
    O <= G.
Proof.
    intros b v e G. split.
    - intros Ty H1. remember O as H eqn:E. revert G E.
      induction H1 as [G Ty|G Ty k H1 IH]; intros G' H2; inversion H2.
    - intros x Ty H1. remember (x ::: Ty) as k eqn:E. 
      remember O as H eqn:F. revert G x Ty E F.
      induction H1 as [G x Ty|G k Ty H1 IH|G x y Ty Sy H1 H2 IH];
      intros G' x' Ty' H3 H4; inversion H4.
Qed.

Lemma ctxInclRefl : forall (b v:Type) (e:Eq v) (G:@Context b v), 
    G <= G.
Proof. intros b v e G. split; auto. Qed.

Lemma ctxInclTrans : forall (b v:Type) (e:Eq v) (G H K:@Context b v),
    G <= H -> H <= K -> G <= K.
Proof. intros b v e G H K [H1 H2] [H3 H4]. split; auto. Qed.

Lemma ctxInclExtendTy : forall (b v:Type) (e:Eq v) (G H:@Context b v) (t:b),
    G <= H -> G ; t ::: * <= H ; t ::: *.
Proof.
    intros b v e G H t [H1 H2]. split.
    - intros t' H3.  remember (G ; t ::: * ) as G' eqn:E.
      revert G H H1 H2 t E. destruct H3 as [G t|G t k H1].
        + intros G' H H2 H3 t' H4. inversion H4. apply FindTyZ.
        + intros G' H H2 H3 t' H4. inversion H4. subst.
          apply FindTyS, H2. assumption.
    - intros x t' H3. constructor. apply H2. apply findVarRev in H3. assumption.
Qed.

Lemma ctxInclExtendVar : forall (b v:Type)(e:Eq v)(G H:@Context b v)(x:v)(Ty:T b),
    G <= H -> G ; x ::: Ty <= H ; x ::: Ty.
Proof.
    intros b v e G H x Ty [H1 H2]. split.
    - intros Sy H3. apply FindTyS, H1. apply findTyRev in H3. assumption.
    - intros x' Ty' H3.
      remember (G ; x ::: Ty) as G' eqn:E. remember (x' ::: Ty') as k eqn:F.
      revert G H x Ty H1 H2 x' Ty' E F.
      destruct H3 as [G x Ty|G k Ty H1|G x y Ty Sy H1 H2];
      intros G' H x' Ty' H3 H4 y' Sy' H5 H6. 
        + inversion H5. apply FindVarZ.
        + inversion H5.
        + inversion H5. subst. apply FindVarS; try assumption. 
          apply H4. assumption.
Qed.
