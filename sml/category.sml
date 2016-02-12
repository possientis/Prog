use "sets.sml";

datatype ('object, 'arrow) Category =
  category of ('arrow -> 'object) *
              ('arrow -> 'object) *
              ('object -> 'arrow) *
              ('arrow * 'arrow -> 'arrow)

datatype 'a Arrow = arrow of ('a Set) * ('a Set) * ('a -> 'a) 

exception Uncomposable

fun setSource(arrow(a,b,f)) = a
fun setTarget(arrow(a,b,f)) = b
fun setIdentity(a) = arrow(a, a, (fn x => x))
fun setCompose(arrow(a,b,f),arrow(b',c,g)) =
  if setEq(b)(b') then
    arrow(a,c, g o f)
  else
    raise Uncomposable 

val FiniteSets = category(setSource, setTarget, setIdentity, setCompose)

