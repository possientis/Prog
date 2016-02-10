// reduced form where objects identified with identity arrows
public interface Category<X>{ // type X viewed as undelying class of arrows
  public X source(X x); // some invariants need to be satisfied: s o s = s = t o s 
  public X target(X x); // some invariants need to be satisfied: s o t = t = t o t
  public X compose(X x, X y); // throw exception unless t(x) = s(y), also invariant (s(xy)=s(x), t(xy)=t(y))
}


interface Group<X>{ // type X viewed as underlying set, on which group structure in defined
  public X identity();
  public X inverse(X x);
  public X compose(X x, X y);
}




