<?php
// one line comment
# another one line comment 
/* multi line or inline comment */
echo "Hello world\n";

// variable names are case sensitive
// function and class names are not !!!!!

echo NULL == NULL;
echo NULL == false; // they are !!!
echo "\n";

// $birthYear, yearsOld are case sensitive
function myAge($birthYear) {
  // function 'date' or 'DATE' case insensitive
  $yearsOld = dAtE('Y') - $birthYear;   
  return $yearsOld . ' year' . ($yearsOld != 1 ? 's' : ''); 
}

echo 'I am currently '.myAge(1981)." old.\n";
echo 'I am currently '.MYAGE(1981)." old.\n";

echo function_exists('myAge')."\n";  // can be handy

// lambda expression / closures
function getAdder($x) {
  return function($y) use ($x) {
    return $x + $y;
  };
}
$adder = getAdder(8);
echo $adder(2)."\n";

class Person {
  public static $count = 0;
  public $firstName;
  public $lastName;
  var $other; // var = public

  public function __construct($firstName, $lastName = ''){  // optional 2nd arg
    $this->firstName = $firstName;
    $this->lastName = $lastName;
    self::$count = self::$count + 1;  // 'self' refers to class
    // Person::$count = Person::$count //also works
  }

  public function greeting(){
    return 'Hello, my name is '.$this->firstName.
      (($this->lastName != '')?(' '.$this->lastName):'').'.';
  }

  public static function staticGreet($firstName, $lastName){
    return 'Hello, my name is '.$firstName.' '.$lastName.'.';
  }
  // setter/getter
  public function set_other($other){
    echo "Inside Person::set_other method.\n";
    $this->other = $other;
  }
  public function get_other(){
    echo "Inside Person::get_other method.\n";
    return $this->other;
  }
  // testing overriding
  public function foo(){
    echo "running Person::foo method\n";
  }
}

echo Person::$count; echo "\n";
$he = new Person('John','Smith');
echo Person::$count; echo "\n";
$she = new Person('Sally','Davis');
echo Person::$count; echo "\n";
$other = new Person('Amine');
echo Person::$count; echo "\n";
echo $he->greeting(); echo "\n";
echo $she->greeting(); echo "\n";
echo $other->greeting(); echo "\n";
echo PERSON::staticGREET('Jane','Doe'); echo "\n"; // method, class names case-insensitive
echo $he->other == NULL; echo "\n";
echo $he->greeting(); echo "\n";
$he->set_other(23);
echo $he->get_other(); echo "\n";
echo strtoupper("this Is QuITe unexpected\n");

// class derivation
class Employee extends Person {
  public function __construct($firstName, $lastName=''){
    Person::__construct($firstName,$lastName);
  }
  // testing overriding
  public function foo(){
    echo "running Employee::foo method\n";
  }
}

// interfaces
interface Shape {
  public function draw();
}

abstract class AbstractShape implements Shape {
}

class Rectangle extends AbstractShape {
  public function draw(){
    print "Inside Rectangle::draw method.\n"; // 'print' works too
  }
}


$we = new Employee('Bob','Diamond');
echo $we->greeting(); echo PHP_EOL;
$we->foo(); // overriding seems to work
$he->foo(); 

$rect = new Rectangle;  // or 'new Rectangle()'
$rect->draw();

echo empty(""); echo PHP_EOL;
echo null == NULL; echo PHP_EOL;

// PHP Arrays are in fact associative arrays, i.e. Map and Dictionaries
$myArray = ["1" => "Hello", "2" => "How are you?", "3" => "Very well ty"];
$yourArray = [];

echo $myArray["1"].PHP_EOL;
echo $myArray["2"].PHP_EOL;
echo $myArray["3"].PHP_EOL;

$myArray["4"] = "This is a new item";
echo $myArray["4"].PHP_EOL;
echo $myArray{"4"}.PHP_EOL;

var_dump($myArray);

$x = ["a","b","c"]; // leave the keys out
var_dump($x);

//echo $myArray["unknown-key"] == NULL; // Alas comment on stderr

unset($myArray["4"]); // to remove an element

var_dump($myArray);

print_r($myArray); // different output from var_dump

$myArray[] = "The item appended";

print_r($myArray);







?>

