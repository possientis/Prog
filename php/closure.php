<?php
$message = 'hello';

$example = function() use ($message) {
  echo $message.PHP_EOL;
};

$example();
$message = 'changing message';
$example();
$message = 'hello';

$example = function() use (&$message) { // capture by reference
  echo $message.PHP_EOL;
};

$example();
$message = 'changing message once more';
$example();


?>
