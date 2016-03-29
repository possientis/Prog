// Flyweight Design Pattern
import java.util.HashMap;

interface Set {
  public String toString();
  public default Set Successor(){ return Union(this,Singleton(this)); } 

  // static factory method
  public static Set Zero(){ return new CZero(); }
  public static Set Singleton(Set x){ return new CSingleton(x); }
  public static Set Union(Set x, Set y){ return new CUnion(x, y); }
  public static Set One(){ return Zero().Successor(); }
  public static Set Two(){ return One().Successor(); }
  public static Set Three(){ return Two().Successor(); }
  public static Set Four(){ return Three().Successor(); }
  public static Set Five(){ return Four().Successor(); }
}

// attempting to create hierarchy of sets using composite design pattern
abstract class CSet implements Set {
  public static long count = 0;
}

class CZero extends CSet {
  public CZero(){count++;}
  @Override
  public String toString(){ return "0"; }
}

class CSingleton extends CSet {
  private final Set element; 
  public CSingleton(Set element){ this.element = element; count++; }
  @Override
  public String toString(){ return "{" + element.toString() + "}"; }
}

class CUnion extends CSet {
  private final Set left;
  private final Set right;
  public CUnion(Set left, Set right){ this.left = left; this.right = right; count++; }
  @Override
  public String toString(){ 
    return left.toString() + "U" + right.toString();
  }
}

class SetManager {
  private int nextHash = 0;
  private final HashMap<Integer,Integer> singletonMap = new HashMap<>();

}

public class Flyweight {
  public static void main(String[] args){

    Set zero  = Set.Zero();
    Set one   = Set.One();
    Set two   = Set.Two();
    Set three = Set.Three(); 
    Set four  = Set.Four(); 
    Set five  = Set.Five(); 

    System.out.println(zero);
    System.out.println(one);
    System.out.println(two);
    System.out.println(three);
    System.out.println(four);
    System.out.println(five);


    System.out.println("Number of objects created: " + CSet.count);
  }
}
