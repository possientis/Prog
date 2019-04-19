Fail Inductive List (M : Type -> Type) (a : Type) : Type :=
| Nil  : List M a
| Cons : M a -> M (List M a) -> List M a
.


Fail Inductive NonStrictlyPos := 
| con : (NonStrictlyPos -> nat) -> NonStrictlyPos
.

Inductive StrictlyPos :=
| con : StrictlyPos -> (nat -> StrictlyPos) -> StrictlyPos
.

Fail Definition applyFun (t:NonStrictlyPos) : nat :=
    match t with
    | con f => f t
    end.

Fail Inductive Mu (a:Type) : Type :=
| mu : (Mu a -> a) -> Mu a
.

Definition Cont r a := (a -> r) -> r.

Fail Inductive ListC r a :=
| NilC : ListC r a
| ConsC: ((a -> r) -> r) -> ((ListC r a -> r) -> r) -> ListC r a
.

Fail Inductive Free f a :=
| pure   : a -> Free f a
| impure : f (Free f a) -> Free f a
.

Inductive Void :=.

Definition Zero (a:Type) : Type := Void.
Definition One  (a:Type) : Type := unit.

Inductive Const (b a: Type) : Type := 
| const : b -> Const b a
.

Fail Inductive FixF f := fixF : f (FixF f) -> FixF f.

Inductive Ext (Shape : Type) (Pos:Shape -> Type) a :=
| ext : forall (s : Shape), (Pos s -> a) -> Ext Shape Pos a
.

Arguments ext {Shape} {Pos} {a} _ _.

Definition absurd (a:Type) : Void -> a :=
    fun p => match p with end.

Definition ShapeOne := unit.
Definition PosOne (s:ShapeOne) := Void.
Definition ExtOne a := Ext ShapeOne PosOne a.

Definition toOne (a:Type) (e:ExtOne a) : One a := tt.

Arguments toOne {a} _.

Definition fromOne (a:Type) (z:One a) : ExtOne a :=
    ext tt (absurd a).

Arguments fromOne {a} _.

Lemma toFromOne : forall (a:Type) (z:One a), toOne (fromOne z) = z.
Proof.
    intros a z. destruct z. unfold toOne. reflexivity.
Qed.

Axiom extensionality : forall (a b:Type) (f g:a -> b),
    (forall (x:a), f x = g x) -> f = g.

Arguments extensionality {a} {b} _ _ _.

Lemma absurd_unique : forall (a:Type) (f:Void -> a), f = absurd a.
Proof.
    intros a f. apply extensionality. intros x. inversion x.
Qed.


Lemma fromToOne : forall (a:Type) (e:ExtOne a), fromOne (toOne e) = e.
Proof.
    intros a [s pos]. unfold PosOne in pos. unfold ShapeOne in s. destruct s.
    unfold toOne. unfold fromOne. rewrite (absurd_unique a pos). 
    reflexivity.
Qed.



