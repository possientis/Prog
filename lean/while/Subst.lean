import Env
import AExp

def Pred : Type := Env -> Prop

def subst (x:string) (a:AExp)(p:Pred) : Pred :=
  λ (s:Env), p (bindVar x a s)
