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
  abstract public boolean isZero(); 
  abstract public boolean isSingleton();
  abstract public boolean isUnion();
}

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
}

class CUnion extends CSet {
  private final Set left;
  private final Set right;
  public CUnion(Set left, Set right){ this.left = left; this.right = right; count++; }
  @Override
  public String toString(){ 
    return left.toString() + "U" + right.toString();
  }
  @Override
  public boolean isZero(){ return false; }
  @Override
  public boolean isSingleton(){ return false; }
  @Override
  public boolean isUnion(){ return true; }
}

class SetManager {
  public static int pairingCantor(int x, int y){
    return (x + y + 1)*(x + y)/2 + y; // '/' is integer division
  }
  private int nextHash = 0;
  private final HashMap<Integer,Integer> singletonMap = new HashMap<>();
  private final HashMap<Integer,Integer> unionMap = new HashMap<>();

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
