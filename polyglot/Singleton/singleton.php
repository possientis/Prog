<?php
// Singleton design pattern

class SingleObject {

  private static $instance = NULL;

  public static function getInstance(){
    if(self::$instance == NULL){
      self::$instance = new SingleObject;
    }
    return self::$instance;
  }

  public function showMessage(){
    echo 'The single object is alive and well'.PHP_EOL;
  }

  private function __construct(){}
}

$object1 = SingleObject::getInstance();
$object1->showMessage();

$object2 = SingleObject::getInstance();
if($object1 === $object2){ // '===' checks for same reference
  echo 'The two objects are the same'.PHP_EOL;
}


?>
