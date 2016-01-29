<?php

class Foo
{
      public $bar;
}

$foo = new Foo;
$foo->bar = function($baz) { echo strtoupper($baz); };
//$foo->bar('lorem ipsum dolor sit amet');

$s = "bar";
$t = "var_dump";
$u = '$foo';

echo $u.PHP_EOL;

// var_dump($foo->bar)
$t($foo->$s);           // wow such flexibility rarely present in other languages

// but there are limits it seems
// $t($u->$s) // this wont work


?>
