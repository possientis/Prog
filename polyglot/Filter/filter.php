<?php
// Filter design pattern

// This pattern allows to use a list of objects and perform
// a filtering operation on that list so as to obtain a new
// list comprised of those objects in the initial list which
// satisfy a given predicate. Since the introduction of
// lambda expressions within Java 8 and the introduction
// of functional interfaces such as Predicate<T>, this 
// pattern is not very useful in practice and amounts 
// mainly to a coding exercise aiming at re-implementing
// the Predicate<T> java interface. This pattern is not
// useful either in functional languages which directly 
// support first class functions and filter operations on lists.

class Predicate {
  public $test;              // the actual predicate function

  public function __construct($func){
    $this->test = $func;
  }

  public function not(){
    $func = $this->test;
    return new Predicate(function($person) use ($func){
      return !$func($person);
    });
  }

  public function pAnd($predicate){ // 'and' keyword, cant use it
    $test1 = $this->test;
    $test2 = $predicate->test;
    return new Predicate(function($person) use ($test1,$test2){
      return !$test1($person) ? false : $test2($person);
    });
  }

  public function pOr($predicate){ // 'or' keyword, cant use it
    $test1 = $this->test;
    $test2 = $predicate->test;
    return new Predicate(function($person) use ($test1,$test2){
      return $test1($person) ? true : $test2($person);
    });
  }

  public static function isEqual($targetRef){
    return new Predicate(function($person) use ($targetRef){
      return $person->equals($targetRef);
    });
  }

  // necessary boiler-plate so closure data member $test can be called as method
  public function __call($method, $args){
    return call_user_func_array($this->$method,$args);  // don't forget 'return'
  }
} 

class Person {

  private $name;
  private $gender;
  private $maritalStatus;

  public function __construct($name, $gender, $maritalStatus){
    $this->name          = $name;
    $this->gender        = $gender;
    $this->maritalStatus = $maritalStatus;

  } 

  public function getName()         { return $this->name; } 
  public function getGender()       { return $this->gender; } 
  public function getMaritalStatus(){ return $this->maritalStatus; } 

  // possible definition of equality
  public function equals($other){
    if(get_class($other) == "Person"){
      return strtoupper($this->getName()) == strtoupper($other->getName());
    }
  }

  public static function people(){
    $list = [
      new Person("Robert","Male","Single"),
      new Person("John","Male","Married"),
      new Person("Laura","Female","Married"),
      new Person("Diana","Female","Single"),
      new Person("Mike","Male","Single"),
      new Person("Bobby","Male","Single")];
    return $list;
  }

  public static function display($list){
    foreach($list as $person){ echo "(".$person->getName()
      . "," . $person->getGender()
      . "," . $person->getMaritalStatus()
      . ")\t";
    }
  }

  public static function filter($list, $predicate){
    if($predicate == NULL) return $list;  //temporary
    return array_filter($list, function($person) use ($predicate){
      return $predicate->test($person); // don't forget 'return'
    });
  }

  // initialization code below class definition
  public static $male;
  public static $female; 
  public static $single;
  public static $singleMale;
  public static $singleOrFemale = NULL;

}

Person::$male = new Predicate(function($person){
  return strtoupper($person->getGender()) == "MALE";
});

Person::$female = new Predicate(function($person){
  return strtoupper($person->getGender()) == "FEMALE";
});

Person::$single = new Predicate(function($person){
  return strtoupper($person->getMaritalStatus()) == "SINGLE";
});

Person::$singleMale = Person::$single->pAnd(Person::$male);
Person::$singleOrFemale = Person::$single->pOr(Person::$female);

$john2 = new Person("John","Male","Married");
$notJohn = Predicate::isEqual($john2)->not();

$people           = Person::people();
$males            = Person::filter($people,Person::$male);
$females          = Person::filter($people,Person::$female);
$singleMales      = Person::filter($people,Person::$singleMale);
$singleOrFemales  = Person::filter($people,Person::$singleOrFemale);
$notJohns         = Person::filter($people,$notJohn);


echo "Everyone:\t\t";         Person::display($people);
echo "\nNot John:\t\t";       Person::display($notJohns);
echo "\nSingle or Female:\t"; Person::display($singleOrFemales);
echo "\nMales:\t\t\t";        Person::display($males);
echo "\nSingle Males:\t\t";   Person::display($singleMales);
echo "\nFemales:\t\t";        Person::display($females);
echo PHP_EOL;

?>

