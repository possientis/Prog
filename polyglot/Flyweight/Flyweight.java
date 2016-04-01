// Flyweight Design Pattern
import java.util.HashMap;

// interface representing the inductive type with constructors:
// (i)    0: X
// (ii)  {}: X -> X
// (iii)  U: X -> X-> X
// This corresponds to the mathematical notion of free algebra
// with type given by the signatures (i) (ii) (iii).
interface Set {
  public String toString();
  public int hashCode();
  // type
  public boolean isZero(); 
  public boolean isSingleton();
  public boolean isUnion();
  // data accessors
  public Set element();
  public Set left();
  public Set right();
  // primitive operators
  public Set singleton();
  public Set union(Set x);
  public static Set singleton(Set x){ return x.singleton(); } 
  public static Set union(Set x, Set y){ return x.union(y); }
  // non
  public default Set successor(){ return union(this.singleton()); }
  public static Set successor(Set x){ return x.successor(); }
}

// attempting to create hierarchy of sets using composite design pattern
abstract class CSet implements Set {
  public static long count = 0;
  protected final SetManager manager = new SetManager();
  public Set singleton(){ return new CSingleton(this); }
  public Set union(Set x){ return new CUnion(this,x); }
}


/*
class HSet implements Set {
  // static
  public static long count = 0;
  private static final SetManager manager = new SetManager();  
  // data
  private final int hash;
  // ctor
  protected HSet(int hash){ this.hash = hash; }
  // zero
  public static Set zero(){ return new HSet(0); }
}
*/


class CZero extends CSet {
  public CZero(){count++;}
  @Override
  public String toString(){ return "0"; }
  @Override
  public boolean isZero(){ return true; }
  @Override
  public boolean isSingleton(){ return false; }
  @Override
  public boolean isUnion(){ return false; }
  @Override
  public Set element(){ 
    throw new UnsupportedOperationException("Empty set has no element"); }
  @Override
  public Set left(){ 
    throw new UnsupportedOperationException("Empty set has no left element"); }
  @Override
  public Set right(){ 
    throw new UnsupportedOperationException("Empty set has no right element"); }
}


class CSingleton extends CSet {
  private final Set element; 
  public CSingleton(Set element){ this.element = element; count++; }
  @Override
  public String toString(){ return "{" + element.toString() + "}"; }
  @Override
  public boolean isZero(){ return false; }
  @Override
  public boolean isSingleton(){ return true; }
  @Override
  public boolean isUnion(){ return false; }
  @Override
  public Set element(){ return element; }
  @Override
  public Set left(){ 
    throw new UnsupportedOperationException("Singleton has no left element"); }
  @Override
  public Set right(){ 
    throw new UnsupportedOperationException("Singleton has no right element"); }
}

class CUnion extends CSet {
  private final Set left;
  private final Set right;
  public CUnion(Set left, Set right){ 
    this.left = left; this.right = right; count++; }
  @Override
  public String toString(){ 
    return left.toString() + "U" + right.toString(); }
  @Override
  public boolean isZero(){ return false; }
  @Override
  public boolean isSingleton(){ return false; }
  @Override
  public boolean isUnion(){ return true; }
  @Override
  public Set element(){
    throw new UnsupportedOperationException("Use 'left' or 'right' on union"); }
  @Override
  public Set left(){ return left; }
  @Override
  public Set right(){ return right; }
}

class SetManager {
  public SetManager(){}
  public static int pairingCantor(int x, int y){
    return (x + y + 1)*(x + y)/2 + y; // '/' is integer division
  }
  private int nextHash = 1;
  private final HashMap<Integer,Integer> singletonMap = new HashMap<>();
  private final HashMap<Integer,Integer> unionMap = new HashMap<>();
  // generatin hash for operators
  public int zeroHash(){ return 0; }
  public int hash(Set x){
    if(x.isZero()){
      return 0;
    } else {
      if(x.isSingleton()){
        Integer elementHash = hash(x.element());
        Integer mappedHash = singletonMap.get(elementHash);
        if(mappedHash == null){ // elementHash not part of singletonMap
          singletonMap.put(elementHash, nextHash); // assigning nextHash to x
          return nextHash++;
        } else {                // elementHash is already part of singletonMap
          return mappedHash;
        }
      } else {
        assert(x.isUnion());
        Integer leftHash = hash(x.left());
        Integer rightHash = hash(x.right());
        int pairHash = pairingCantor(leftHash, rightHash);
        Integer mappedHash = unionMap.get(pairHash);
        if(mappedHash == null){ // pairHash not part of unionMap
          unionMap.put(pairHash, nextHash); // assigning nextHash to x
          return nextHash++;
        } else {                // pairHash is already part of unionMap
          return mappedHash;
        }
      }
    }
  }
}


public class Flyweight {
  public static void main(String[] args){

    SetManager manager = new SetManager();
    Set zero  = new CZero();
    Set one   = zero.successor();
    Set two   = one.successor();
    Set three = two.successor();
    Set four  = three.successor();
    Set five  = four.successor();
    Set six   = five.successor();
    Set seven = six.successor();
    Set eight = seven.successor();
    Set nine  = eight.successor();
    Set ten   = nine.successor();

    System.out.println("Hash of zero is:  " + manager.hash(zero)); 
    System.out.println("Hash of one is:   " + manager.hash(one)); 
    System.out.println("Hash of two is:   " + manager.hash(two)); 
    System.out.println("Hash of three is: " + manager.hash(three)); 
    System.out.println("Hash of four is:  " + manager.hash(four)); 
    System.out.println("Hash of five is:  " + manager.hash(five)); 
    System.out.println("Hash of six is:   " + manager.hash(six)); 
    System.out.println("Hash of seven is: " + manager.hash(seven)); 
    System.out.println("Hash of eight is: " + manager.hash(eight)); 
    System.out.println("Hash of nine is:  " + manager.hash(nine)); 
    System.out.println("Hash of ten is:   " + manager.hash(ten)); 

    System.out.println(zero); 
    System.out.println(one); 
    System.out.println(two); 

    System.out.println("Number of CSet objects created: " + CSet.count);
  }
}
