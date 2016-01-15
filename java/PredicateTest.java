import java.util.*;

@FunctionalInterface
interface IPredicate<T> {
  public boolean Test(T t);
  public default IPredicate<T> negate(){
    return t -> !Test(t);
  }
  public static <T> IPredicate<T> isEqual(Object targetRef){
    return t -> Objects.equals(t,targetRef);
  }
  public default IPredicate<T> and(IPredicate<? super T> other){
    return t ->  !Test(t) ? false : other.Test(t);
  }

  public default IPredicate<T> or(IPredicate<? super T> other){
    return t -> Test(t) ? true : other.Test(t);
  }

}

public class PredicateTest {

  public static void main(String[] args){
    IPredicate<String> p = s -> s.equals("hello");
    IPredicate<Integer> q = n -> (n == 5);
    IPredicate <String> _p = p.negate();
    IPredicate<String> r = IPredicate.isEqual("hello");
    IPredicate<String> _r = r.negate();

    String s1 = "hello";
    String s2 = "Hello";

    System.out.println(p.Test(s1) + ":" + _p.Test(s1));
    System.out.println(r.Test(s1) + ":" + _r.Test(s1));
    System.out.println(p.Test(s2) + ":" + _p.Test(s2));
    System.out.println(r.Test(s2) + ":" + _r.Test(s2));
    System.out.println(q.Test(5));
    System.out.println(q.Test(0));

    System.out.println(p.and(_p).Test("anything"));
    System.out.println(p.or(_p).Test("anything"));
  }

}
