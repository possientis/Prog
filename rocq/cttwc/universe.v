(* universe: type whose inhabitants are types:
    - Prop
    - Set

    Prop <= Set, i.e.

    t : Prop
    --------
    t : Set

    T1 : T2 : T3 : .....
    Prop <= T1 <= T2 <= T3 <= ...

    Set  : T2   Set = T1
    Prop : T2

    closure rules:

      s:Ti  t:Prop       s:Ti  t:T1
    -----------------  ---------------
     A(x:s).t : Prop    A(x:s).t : Ti

    Prop is closed under all quantifications including 'big' ones.
    In contrast A(x:Ti).t is not in universe Ti
    Prop is called impredicative since closed under big quantifications 

*)


