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
    return $list;
  }

  public static $male = NULL;
  public static $female = NULL;
  public static $single = NULL;
  public static $singleMale = NULL;
  public static $singleOrFemale = NULL;

}

$john2 = new Person("John","Male","Married");
$notJohn = NULL;

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

?>

