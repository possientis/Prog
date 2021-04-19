Require Import Logic.Class.Eq.

Require Import Logic.STLC.Valid.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Typing.
Require Import Logic.STLC.Context.

Inductive Judgement2 (b v:Type) (eq:Eq v): Context -> Typing -> Prop :=
| JAnn : forall (G:Context) (e:Exp b v) (Ty:T b),
    Valid G                                     ->  (* superfluous              *)
    G :> Ty                                     ->  (* superfluous              *)
    Judgement2 b v eq G (e >: Ty)               ->
    Judgement2 b v eq G ((e :: Ty) >: Ty)    
| JVar : forall (G:Context) (x:v) (Ty:T b),
    Valid G                                     -> 
    G :> Ty                                     ->  (* superfluous              *)
    G :>> x ::: Ty                              -> 
    Judgement2 b v eq G (`x >: Ty)            
| JApp : forall (G:Context) (e1 e2:Exp b v) (Ty Ty':T b),
    Valid G                                     ->  (* superfluous              *)
    G :> Ty                                     ->  (* superfluous              *)
    G :> Ty'                                    ->  (* superfluous              *)
    Judgement2 b v eq G (e1 >: Ty :-> Ty')      ->  
    Judgement2 b v eq G (e2 >: Ty)              -> 
    Judgement2 b v eq G (e1 $ e2 >: Ty')        
| JLam : forall (G:Context) (x:v) (e:Exp b v) (Ty Ty':T b),
    Valid G                                     ->  
    G :> Ty                                     ->  
    Judgement2 b v eq (G;x ::: Ty) (e >: Ty')   ->  
    Judgement2 b v eq G ((\x ~> e) >: Ty :-> Ty')
.


