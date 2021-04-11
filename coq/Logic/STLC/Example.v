Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.STLC.Eval.
Require Import Logic.STLC.Value.
Require Import Logic.STLC.Subst.
Require Import Logic.STLC.Valid.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Typing.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.Replace.
Require Import Logic.STLC.Context.

Definition id (b v:Type)(x:v) : Exp b v := \x ~> `x.

Arguments id {b} {v}.

(* This will not have the right semantics unless x and y are distinct           *)
Definition const (b v:Type) (x y:v) : Exp b v := \x ~> \y ~> `x.

Arguments const {b} {v}.

(* Annotated identity applied to variable y reduces to variable y               *)
Lemma idAnn : forall (b v:Type) (e:Eq v) (x y:v) (Ty:T b),
    (id x :: Ty :-> Ty) $ `y >>> `y.
Proof.
    intros b v e x y Ty. apply (EAppL (id x :: Ty :-> Ty) `x _ _ x).
    - apply VVar.
    - apply VVar.
    - constructor. apply VLam, VVar. apply ELam.
        + apply VVar.
        + constructor.
    - rewrite substVar. rewrite replace_x. constructor.
Qed.

(* Annotated const applied to identity and variable u reduces to identity       *)
(* Note that we need the variables x and y to be distinct for this to hold      *)
Lemma constAnn : forall (b v:Type) (e:Eq v) (x y z u:v) (Ty Ty' : T b),
    x <> y -> 
    (const x y :: (Ty' :-> Ty') :-> Ty :-> Ty' :-> Ty') $ (id z) $ `u >>> id z. 
Proof.
    intros base v e x y z u Ty Ty' H1. apply (EAppL _ (id z) _ _ y).
    - apply VLam, VVar.
    - apply VLam, VVar.
    - apply (EAppL _ (\y ~> `x) _ _ x). 
        + apply VLam, VVar.
        + apply VLam, VLam, VVar.
        + constructor.
            { apply VLam, VLam, VVar. }
            { constructor.
                { apply VLam, VVar. }
                { constructor.
                    { apply VVar. }
                    { constructor. }}}
        + constructor. 
            { apply VLam, VVar. }
            { destruct (in_dec eqDec x (y :: nil)) as [H2|H2].
                { exfalso. destruct H2 as [H2|H2].
                    { auto. }
                    { inversion H2. }}
                { rewrite replace_x. apply ELam.
                    { apply VVar. }
                    { apply EVar. }}}
    - apply ELam.
        + apply VVar.
        + destruct (in_dec eqDec z (z :: nil)) as [H2|H2].
            { apply EVar. }
            { exfalso. apply H2. left. reflexivity. }
Qed.

(* An example of valid context.                                                 *)
Lemma Valid1 : forall (b v:Type) (t t':b) (x:v),
    Valid   ( O 
            ; t  ::: * 
            ; t' ::: * 
            ; x  ::: (('t' :-> 't') :-> 't :-> 't' :-> 't')
            ).
Proof.
    intros b v t t' x. apply ValidV.
    - apply ValidT, ValidT, ValidO.
    - apply TFun.
        + apply TFun; apply TVar, FindTZ.
        + apply TFun.
            { apply TVar, FindTS, FindTZ. }
            { apply TFun; apply TVar, FindTZ. }
Qed.

Lemma Typing1 : forall (b v:Type)(eq:Eq v)(t:b)(x y:v),
    O ; t ::: * ; y ::: 't :- (id x :: 't :-> 't) $ `y >: 't.
Proof.
    intros b v eq t x y. apply JApp with 't.
    - apply JAnn, JLam.
        + apply ValidV.
            { apply ValidT, ValidO. }
            { apply TVar, FindTZ. }
        + apply TVar, FindTS, FindTZ.
        + apply JVar.
            { apply ValidV.
                { apply ValidV.
                    { apply ValidT, ValidO. }
                    { apply TVar, FindTZ. }}
                { apply TVar, FindTS, FindTZ. }}
            { apply FindVZ. }
    - apply JVar.
        + apply ValidV.
            { apply ValidT, ValidO. }
            { apply TVar, FindTZ. }
        + apply FindVZ.
Qed.

Lemma Typing2 : forall (b v:Type) (eq:Eq v) (t t':b) (x y z u:v),
    x <> y ->
        O ; t ::: * ; u ::: 't ; t' ::: * 
            :-
        (const x y :: ('t' :-> 't') :-> 't :-> 't' :-> 't') $ (id z) $ `u
            >:
        't' :-> 't'.
Proof.
    intros b v eq t t' x y z u H1. apply JApp with 't.
    - apply JApp with ('t' :-> 't').
        + apply JAnn, JLam.
            { apply ValidT, ValidV.
                { apply ValidT, ValidO. }
                { apply TVar, FindTZ. }}
            { apply TFun; apply TVar, FindTZ. }
            { apply JLam.
                { apply ValidV.
                    { apply ValidT, ValidV. 
                        { apply ValidT, ValidO. }
                        { apply TVar, FindTZ. }}
                    { apply TFun; apply TVar, FindTZ. }}
                { apply TVar, FindTS, FindTS, FindTS, FindTZ. }
                { apply JVar.
                    { apply ValidV.
                        { apply ValidV.
                            { apply ValidT, ValidV.
                                { apply ValidT, ValidO. }
                                { apply TVar, FindTZ. }}
                            { apply TFun; apply TVar, FindTZ. }}
                        { apply TVar, FindTS, FindTS, FindTS, FindTZ. }}
                    { apply FindVS; try assumption. apply FindVZ. }}}
        + apply JLam.
            { apply ValidT, ValidV.
                { apply ValidT, ValidO. }
                { apply TVar, FindTZ. }}
            { apply TVar, FindTZ. }
            { apply JVar.
                { apply ValidV.
                    { apply ValidT, ValidV.
                        { apply ValidT, ValidO. }
                        { apply TVar, FindTZ. }}
                    { apply TVar, FindTZ. }}
                { apply FindVZ. }}
    - apply JVar.
        + apply ValidT, ValidV.
            { apply ValidT, ValidO. }
            { apply TVar, FindTZ. }
        + apply FindVK, FindVZ.
Qed.
