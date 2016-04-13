// see scala discussion on invariant, covariant, contravariant
// generic types. In java, arrays are covariant by default. However,
// they are not immutable (hence has setters with arguments in contravariant
// position). This create an inconsistency in type checking

public class CovariantArray {
  public static void main(String[] args){
    String[] a1 = {"abc"};
    Object[] a2 = a1;
//    a2[0] = new Integer(17);        // yet this does not compile
    Object[] a3 = {new Integer(17)};  // this is ok
  }
}
