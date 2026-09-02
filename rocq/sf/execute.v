Require Import nat.
Require Import list.
Require Import dictionary.
Require Import state.
Require Import ISA.

Fixpoint s_execute (e:State) (stack:list nat)(prog:list sinstr) : list nat :=
  match prog with
  | []      => stack  (* returns stack as it currently is *)
  | (i::is) => match i with
               | SPush n  => s_execute e (n::stack) is
               | SLoad k  => s_execute e ((e k)::stack) is
               | SPlus    => match stack with
                             | []         => s_execute e stack is (* error *)
                             | [x]        => s_execute e stack is (* error *)
                             | x::y::st'  => s_execute e ((y+x)::st') is 
                            end
               | SMinus   => match stack with
                             | []         => s_execute e stack is (* error *)
                             | [x]        => s_execute e stack is (* error *)
                             | x::y::st'  => s_execute e ((y-x)::st') is 
                            end
               | SMult    => match stack with
                             | []         => s_execute e stack is (* error *)
                             | [x]        => s_execute e stack is (* error *)
                             | x::y::st'  => s_execute e ((y*x)::st') is 
                            end
                end
  end.


Lemma s_execute_app : forall (e:State) (stack:list nat)(p1 p2:list sinstr),
  s_execute e stack (p1 ++ p2) = s_execute e (s_execute e stack p1) p2. 
Proof.
  intros e stack p1. revert stack. induction p1 as [|i is IH].
  - reflexivity.
  - intros stack p2. destruct i.
    + simpl. rewrite IH. reflexivity.
    + simpl. rewrite IH. reflexivity.
    + destruct stack as [|n stack].  
      { simpl. rewrite IH. reflexivity. } 
      { destruct stack as [|n' stack].
        { simpl. rewrite IH. reflexivity. }
        { simpl. rewrite IH. reflexivity. } } 
    + destruct stack as [|n stack].  
      { simpl. rewrite IH. reflexivity. } 
      { destruct stack as [|n' stack].
        { simpl. rewrite IH. reflexivity. }
        { simpl. rewrite IH. reflexivity. } } 
    + destruct stack as [|n stack].  
      { simpl. rewrite IH. reflexivity. } 
      { destruct stack as [|n' stack].
        { simpl. rewrite IH. reflexivity. }
        { simpl. rewrite IH. reflexivity. } } 
Qed.
          

