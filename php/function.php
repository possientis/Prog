<?php

class Foo
{
      public $bar;  // closure object data member

      // some regular method
      public function baz($message){
        echo $message.PHP_EOL;
      }

      // you need to set this up if you want to call
      // a closure object data member as a regular method
      // Why this is the case is unclear
      public function __call($method, $args){
        echo "I am here ...\n";
        $closure = $this->$method;
        call_user_func_array($closure,$args);
      }
}

$foo = new Foo; 
// some closure object
$func = function($baz) { echo strtoupper($baz).PHP_EOL; };
// closure object assigned to data member
$foo->bar = $func;
// cannot call data member (despite being closure object)
// unless __call class method as been set up ...
$foo->bar('lorem ipsum dolor sit amet');
// regular method calls unaffected by __call method
$foo->baz('this is a normal method call');

// additional comments
$myArray = ["This is a message"];
// this feels a little bit like the Scheme 'apply' function
call_user_func_array($func,$myArray);


?>
