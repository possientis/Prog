<?php

trait A {
  public function smallTalk() {
    echo 'a';
  }
  public function bigTalk() {
    echo 'A';
  }
}

trait B {
  public function smallTalk() {
    echo 'b';
  }
  public function bigTalk() {
    echo 'B';
  }
}

class Talker {
  use A, B {
    B::smallTalk insteadof A;
    A::bigTalk insteadof B;
  }
}

class Aliased_Talker {
  use A, B {
    B::smallTalk insteadof A;
    A::bigTalk insteadof B;
    B::bigTalk as talk;
  }
}

$a = new Talker();
$a->smallTalk();  // expecting 'b'
$a->bigTalk();    //expecting 'A'
echo PHP_EOL;
$a = new Aliased_Talker();
$a->smallTalk();  // expecting 'b'
$a->bigTalk();    // expecting 'A'
$a->talk();       // expecting 'B'
echo PHP_EOL;

trait HelloWorld {
  public function sayHello() {
    echo 'Hello World!';
  }
}

// Change visibility of sayHello
class MyClass1 {
  use HelloWorld { sayHello as protected; }
  public function test(){
    $this->sayHello();
  }
}

// Alias method with changed visibility
// sayHello visibility not changed
class MyClass2 {
  use HelloWorld { sayHello as private myPrivateHello; }
}
$a = new MyClass1();
//$a->sayHello(); // protected, not gonna work
$a->test();
echo PHP_EOL;




?>

