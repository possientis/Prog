<?php

// Example 1: Way of partially lifting restrictions on multiple inheritance
trait ezcReflectionReturnInfo {
  function getReturnType() { /*1*/ }
  function getReturnDescription() { /*2*/ }
}

class ezcReflectionMethod extends ReflectionMethod {
      use ezcReflectionReturnInfo;
          /* ... */
}


class ezcReflectionFunction extends ReflectionFunction {
      use ezcReflectionReturnInfo;
          /* ... */
}

// Example 2: Traits takes precedence over base class
class Base {
  public function sayHello() {
    echo 'Hello ';
  }
}

trait SayWorld {
  public function sayHello() {
    parent::sayHello();
    echo 'World!';
  }
}

class MyHelloWorld extends Base {
      use SayWorld;   // trait will override inherited base class method
}

$o = new MyHelloWorld();
$o->sayHello();


// Example 3: Traits does not take precedence over derived class
trait HelloWorld {
  public function sayHello() {
    echo 'Hello World!';
  }
}

class TheWorldIsNotEnough {
  use HelloWorld;     // however trait will not override, derived class method
  public function sayHello() {
    echo 'Hello Universe!';
  }
}

$o = new TheWorldIsNotEnough();
$o->sayHello();

?>
