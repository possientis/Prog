// dependent type , generic class Cell1[T] is 'invariant'
// in type T. This means that it is neither 'covariant'
// nor 'contravariant'. covariant means that if S is a 
// subtype of T, then Cell1[S] is a subtype of Cell1[T]
// which is not the case here (in scala invariant is assumed
// by default). contravariant means that if S <: T then
// Cell1[T] <: Cell1[S].

 
// this is (by default) invariant in T. not covariant
// nor contravariant
class Cell1[T](init:T){
  private[this] var current = init
  def get = current
  def set(x:T){ current = x }
}

val c1 = new Cell1("abc")
// class is not covariant. so Cell1[String] is not a subtype
// of Cell1[Any]. Hence c1 cannot be assigned to c2.
// val c2: Cell1[Any] = c1  // compiler error



// using the annotation '+' allows to declare generic class
// as covariant. However, the setter set(x: T) has T in 
// 'contravariant' position. If S is a subtype of T, then
// Cell2[S] cannot possibly be a subtype of Cell2[T]. 
// Indeed, if Cell2[S] <: Cell2[T] then you can take 
// an object c:Cell2[S] and assign it to a variable of
// c':Cell2[T]. But then you can take t:T and call the 
// setter on c' as in c'.set(t). In doing so, you assign
// t:T to a variable current:S. This cannot work.
// So if you wish to declare Cell2 as covariant, you need
// to remove the setter.
class Cell2[+T](init:T){  // '+' for covariant , S<:T -> Cell2[S] <: Cell2[T]
  private[this] var current = init
  def get = current
//  def set(x:T){ current = x }   // compiler error
}

// using the annotation '-' allows to declare generic class
// as contravariant in T. However, the getter get has T in
// in 'covariant' position. If S is a subtype of T, then
// Cell3[T] cannot possibly be a subtype of Cell2[S]. 
// Otherwise, from t:T we could create Cell3(t) which we
// could then assign to a variable of type Cell3[S], and
// using the getter, we could then assign t to a variable
// of type S.
// So if you wish to declare Cell3 as contravariant, you
// need to remove the getter.
 
class Cell3[-T](init:T){  // '-' for contravariant, S<:T -> Cell3[T] <: Cell3[S]
  private[this] var current = init
//  def get = current           // compiler error
  def set(x:T){ current = x }
}


// unlike java, scala arrays are invariant, not covariant
val a1 = Array("abc")
//Note: java.lang.String <: Any, but class Array is invariant in type T.
// val a2: Array[Any] = a1      // compiler error

// this cast will succeed, but you may later have runtime exception.
val a2: Array[Any] = a1.asInstanceOf[Array[Any]]
val a3: Array[Object] = a1.asInstanceOf[Array[Object]]  // object in scala?


// mutability is not the only issue.
// If a generic parameter type appears as the type of a method parameter, 
// the containing data type may not be covariant.





