// Flyweight Design Pattern
import java.util.HashMap;

// The main idea of the flyweight design pattern is to store objects
// in a dictionary so they can be reused, rather than new objects be
// created. This pattern is particularly well suited to classes of 
// immutable objects which is the case we shall consider here. Because
// dictionaries cannot exist without keys, the flyweight design pattern
// is closely related to the question of hashing.
//
// We shall consider the example of an inductive type Set with the three
// constructors (i) Zero : Set,  (ii) Singleton : Set-> Set and (iii)
// Union : Set -> Set -> Set. The type Set therefore corresponds to 
// the free algebra generated by a single element 0 (the empty set) and
// the operators x -> {x} and x,y -> xUy. Although, the questions of preorder
// (inclusion) and equivalence between sets are very important, we shall 
// not consider it here and simply look at elements of type Set as syntactic
// objects. A typical OOP implementation is based on the composite  design 
// pattern which we shall adopt in this example.
//
// Objects (which are immutable) are supposed to be reused, not created.
// So the constructors of the class Set (and its subclasses) should not
// be used directly. Instead, the class should provide static factory 
// functions for 0, {x} and xUy. However, these factory functions should 
// not be simple wrappers around class constructors and should instead 
// check whether an object has previously been created.
//
// Fundamentally, we need to maintain a dictionary of created objects and
// we shall design a separate class SetManager to handle this dictionary.
// In fact the factory functions 0, {x}, xUy will be delegated to the class
// SetManager and Set will simply pass on the client's requests for object
// retrieval (or construction) to SetManager via a static member embedded
// in the class Set. As objects are being created and stored into the 
// manager's dictionary, dynamic hash values will be generated and assigned 
// to objects. The handling of hash values will also be performed by SetManager.
//
// It is possible to consider static algorithms for hash values. However, 
// these often do not guarantee that two objects with equal hash are equal. 
// It is nice to know that a static hash function is a (mathematically) 
// injective mapping. In the case at hand, such function exist but are 
// computationally unusable due to their rapid growth. Using dynamic hashing, 
// although not specifically called for by the flyweight design pattern, 
// provides the convenience of producing truly unique hashes, which grow very 
// slowly (a hash counter is incremented at each object creation). 
//
// So this example illustrate a case of flyweight design pattern, as well
// as proposing a scheme for the generation of dynamic hash values. 


// standard composite pattern with abstract base class, and three concrete
// subclasses corresponding to each constructor of the inductive type Set
abstract class Set {
  // Additionally to composite pattern, we include a static manager
  // whose role is threefold: (i) serve as factory object (ii) maintain
  // dictionaty of existing object and (iii) handle dynamic hash generation
  private static final SetManager manager = new SetManager();
  // Additionally to composite pattern, each object maintains an immutable
  // hash code whose value is determined at runtime by the manager at creation. 
  private final int hash;
  protected Set(int hash)               { this.hash = hash; }
  @Override public int hashCode()       { return hash; }
  // The inductive type provides an interface of static factory methods 
  // which corresponds to the type constructors. However, contrary to standard
  // composite pattern, these factory methods actually delegate the work
  // of object creation of the manager
  public static Set zero()              { return manager.zero(); }
  public static Set singleton(Set x)    { return manager.singleton(x); }
  public static Set union(Set x, Set y) { return manager.union(x,y); }
  // convenience function
  public static Set successor(Set x)    { return union(x, singleton(x)); }
  // implemented by subclasses
  public abstract String toString();
  public abstract boolean isZero();
  public abstract boolean isSingleton();
  public abstract boolean isUnion();
  public abstract Set element();
  public abstract Set left();
  public abstract Set right();
  // debug
  public static void debug(){ manager.debug(); }
}

class Zero extends Set {
  protected Zero(int hash)                { super(hash); }
  @Override public String toString()      { return "0"; }
  @Override public boolean isZero()       { return true; }
  @Override public boolean isSingleton()  { return false; }
  @Override public boolean isUnion()      { return false; }
  @Override public Set element(){ throw new UnsupportedOperationException(); }
  @Override public Set left()   { throw new UnsupportedOperationException(); }
  @Override public Set right()  { throw new UnsupportedOperationException(); }
}

class Singleton extends Set {
  private final Set element; 
  protected Singleton(Set element, int hash){ 
    super(hash); 
    this.element = element; }
  @Override public String toString()      { return "{" + element + "}"; }
  @Override public boolean isZero()       { return false; }
  @Override public boolean isSingleton()  { return true; }
  @Override public boolean isUnion()      { return false; }
  @Override public Set element()          { return element; }
  @Override public Set left()   { throw new UnsupportedOperationException(); }
  @Override public Set right()  { throw new UnsupportedOperationException(); }
}

class Union extends Set {
  private final Set left;
  private final Set right;
  protected Union(Set left, Set right, int hash){ 
    super(hash);
    this.left = left; 
    this.right = right; }
  @Override public String toString()    { return left + "U" + right; }
  @Override public boolean isZero()     { return false; }
  @Override public boolean isSingleton(){ return false; }
  @Override public boolean isUnion()    { return true; }
  @Override public Set left()           { return left; }
  @Override public Set right()          { return right; }
  @Override public Set element(){ throw new UnsupportedOperationException(); }
}

class SetManager {
  // The manager maintains various dictionaries. The main dictionary is objectMap,
  // which given a hash code, returns a previously constructed object. However,
  // The manager needs to implement the factory methods corresponding to the 
  // three constructors of the inductive type Set. Implementing the zero()
  // method is easy. The manager always assigns 0 as its hash code and creates
  // a single object which is stored once and for all in the objectMap dictionary.
  // The method zero() simply returns a reference to the existing object.
  // In order to implement singleton(x) (returning the object {x} from x), the 
  // manager needs to quickly establish whether (given the set x and its hash code)
  // the set {x} has already been created. However, the manager cannot simply query
  // the objectMap dictionary because it does not know what dynamic hash code the
  // singleton {x} was assigned (assuming it already exists). This is why the 
  // manager maintains an additional dictionary 'singletonMap' which stores the 
  // hash code of {x} given the hash code of x. Hence by querying the dictionary 
  // singletonMap, the manager is able to establish whether {x} already exists, 
  // and if so, what its hash code is. Given the hash code of {x} it can simply 
  // query objectMap and return the appropriate object. In the case when the object
  // {x} does not already exist, the manager assigns the current value of 
  // 'nextHash' to the object {x}, then creates the object using this hash value, 
  // and before it returns the object, the manager updates objectMap with the new 
  // object and singletonMap with the link between the hash of x and that of {x}. 
  // In order to implement the factory method union(x,y), a similar scheme is 
  // adopted which requires a new dictionary unionMap. This map could have been 
  // implemented with pairs as keys, but we decided to keep using integers, and 
  // simply map pairs of ints to ints with the Cantor function.

  private int nextHash = 1; // next hash value of whichever object is created
  private final HashMap<Integer,Integer> singletonMap = new HashMap<>();
  private final HashMap<Integer,Integer> unionMap     = new HashMap<>();
  private final HashMap<Integer, Set> objectMap       = new HashMap<>();

  public SetManager(){ objectMap.put(0, new Zero(0)); } // empty set added to map

  public static int pairingCantor(int x, int y){
    return (x + y + 1)*(x + y)/2 + y; // '/' is integer division
  }
  // factory function
  public Set zero(){ return objectMap.get(0); }

  public Set singleton(Set x){
    int hash = x.hashCode();
    Integer mappedHash = singletonMap.get(hash);// finding out whether {x} exists
    if(mappedHash == null){                     // singleton {x} is unknown
      singletonMap.put(hash, nextHash);         // nextHash allocated to {x} 
      Set object = new Singleton(x, nextHash);  // creating {x}
      objectMap.put(nextHash, object);          // saving {x} for future reference
      nextHash++;                               // for future hash allocation
      return object;
    } else {                                    // singleton {x} is known        
      return objectMap.get(mappedHash);         // simply retrieve object from hash
    }
  }
  public Set union(Set x, Set y){
    int hx = x.hashCode();
    int hy = y.hashCode();
    int hash = pairingCantor(hx, hy);
    Integer mappedHash = unionMap.get(hash);    // finding out whether xUy exists
    if(mappedHash == null){                     // union xUy is unknown 
      unionMap.put(hash, nextHash);             // nextHash allocated to xUy
      Set object = new Union(x, y, nextHash);   // creating xUy
      objectMap.put(nextHash, object);          // saving xUy for future reference
      nextHash++;                               // for future hash allocation
      return object;
    } else {                                    // union xUy is known
      return objectMap.get(mappedHash);         // simply retrieve object from hash
    }
  }

  public void debug(){
    for(int i = 0; i< nextHash; ++i){
      System.out.println("hash = " + i + ": " + objectMap.get(i));
    }
  }
}

public class Flyweight {
  public static void main(String[] args){

    Set zero  = Set.zero();
    Set one   = Set.successor(zero);
    Set two   = Set.successor(one);
    Set three = Set.successor(two);
    Set four  = Set.successor(three);
    Set five  = Set.successor(four);
    Set.debug();
  }
}