<?php
// Flyweight Design Pattern

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
  private static $manager;
  public static function init()       { self::$manager = new SetManager; }
  // Additionally to composite pattern, each object maintains an immutable
  // hash code whose value is determined at runtime by the manager at creation. 
  private $hash;
  public function __construct($hash)  { $this->hash = $hash; }
  public function hashCode()          {  return $this->hash; }
  // the inductive type provides an interface of static factory methods 
  // which corresponds to the type constructors. however, contrary to standard
  // composite pattern, these factory methods actually delegate the work
  // of object creation of the manager
  public static function zero()       { return self::$manager->zero(); }
  public static function singleton($x){ return self::$manager->singleton($x); }
  public static function union($x,$y) { return self::$manager->union($x,$y); }
  // convenience function
  public static function successor($x){ return Set::union($x,Set::singleton($x)); }
  public static function debug()      { return self::$manager->debug(); } 
  // implemented by subclasses
  public abstract function __toString();
  public abstract function isZero();
  public abstract function isSingleton();
  public abstract function isUnion(); 
  public abstract function element(); 
  public abstract function left(); 
  public abstract function right(); 
}

Set::init(); // initialization of static private data member


class Zero extends Set {
  public function __construct($hash)  { parent::__construct($hash); }
  public function __toString()        { return "0"; }
  public function isZero()            { return true; }
  public function isSingleton()       { return false; }
  public function isUnion()           { return false; }
  public function element()           { throw new BadFunctionCallException; }
  public function left()              { throw new BadFunctionCallException; }
  public function right()             { throw new BadFunctionCallException; }
}

class Singleton extends Set {
  private $element;

  public function __construct($x, $hash){ 
    parent::__construct($hash); 
    $this->element = $x;        
  }

  public function __toString()          { return "{{$this->element}}"; } 
  public function isZero()              { return false; }
  public function isSingleton()         { return true; }
  public function isUnion()             { return false; }
  public function element()             { return $this->element; }
  public function left()                { throw new BadFunctionCallException; }
  public function right()               { throw new BadFunctionCallException; }
}

class Union extends Set {
  private $left;
  private $right;

  public function __construct($x,$y,$hash){ 
    parent::__construct($hash); 
    $this->left   = $x;        
    $this->right = $y;         
  } 

  public function __toString()          { return "{$this->left}U{$this->right}"; } 
  public function isZero()              { return false; }
  public function isSingleton()         { return false; }
  public function isUnion()             { return true; }
  public function left()                { return $this->left; }
  public function right()               { return $this->right;}
  public function element()             { throw new BadFunctionCallException; }
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

  public static function pairingCantor($x,$y){
    // need explicit cast to int to avoid warning from 'array_key_exists' 
    return (int) round(($x + $y + 1)*($x + $y)/2 + $y); // cast to int
  }
  private $nextHash     = 1;
  private $singletonMap = [];
  private $unionMap     = [];
  private $objectMap    = []; 

  public function __construct(){ $this->objectMap[0] = new Zero(0); }
   
  public function zero()        { return $this->objectMap[0]; }

  public function singleton($x) {
    $hash = $x->hashCode();
    $singletonExists = array_key_exists($hash, $this->singletonMap);
    if($singletonExists == false){
      $this->singletonMap[$hash] = $this->nextHash; // nextHash allocated to {x}
      $object = new Singleton($x, $this->nextHash); // creating {x}
      $this->objectMap[$this->nextHash] = $object;  // saving {x} for future ref
      $this->nextHash += 1;                         // for future hash allocation
      return $object;
    } else {
      $mappedHash = $this->singletonMap[$hash];
      return $this->objectMap[$mappedHash];
    }
  }

  public function union($x,$y)  {
    $hx = $x->hashCode();
    $hy = $y->hashCode();
    $hash = SetManager::pairingCantor($hx,$hy);
    $unionExists = array_key_exists($hash, $this->unionMap);
    if($unionExists == false){
      $this->unionMap[$hash] = $this->nextHash;     // nextHash allocated to xUy
      $object = new Union($x, $y, $this->nextHash); // creating xUy
      $this->objectMap[$this->nextHash] = $object;  // saving xUy for future ref
      $this->nextHash += 1;
      return $object;
    } else {
      $mappedHash = $this->unionMap[$hash];
      return $this->objectMap[$mappedHash];
    }
  }

  public function debug(){
    for($i = 0; $i < $this->nextHash; ++$i){
      echo "hash = {$i}: {$this->objectMap[$i]}\n";
    }
  }

}

// main
$zero   = Set::zero();
$one    = Set::successor($zero); 
$two    = Set::successor($one); 
$three  = Set::successor($two); 
$four   = Set::successor($three); 
$five   = Set::successor($four); 
Set::debug();

?>