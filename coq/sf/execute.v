Require Import nat.
Require Import list.
Require Import dictionary.
Require Import state.
Require Import compile.

Fixpoint s_execute (e:State) (stack:list nat)(prog:list sinstr) : list nat :=
  match prog with
  | []      => stack  (* returns stack as it currently is *)
  | (i::is) => match i with
               | SPush n  => s_execute e (n::stack) is
               | SLoad k  => s_execute e ((e k)::stack) is
               | SPlus    => match stack with
                             | []         => stack  (* error condition *)
                             | [x]        => stack  (* error condition *)
                             | x::y::st'  => s_execute e ((x+y)::st') is 
                            end
               | SMinus   => match stack with
                             | []         => stack  (* error condition *)
                             | [x]        => stack  (* error condition *)
                             | x::y::st'  => s_execute e ((y-x)::st') is 
                            end
               | SMult    => match stack with
                             | []         => stack  (* error condition *)
                             | [x]        => stack  (* error condition *)
                             | x::y::st'  => s_execute e ((x*y)::st') is 
                            end
                end
  end.


