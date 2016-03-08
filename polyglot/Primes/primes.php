<?php
// This PHP implementation is a failure in terms of performance

// quick and dirty implementation of infinite streams
// (which can be finite). We have not defined the empty stream.
class Cell{
  private $car;
  private $cdr;
  private function __construct($first, $rest){
    $this->car = $first;
    $this->cdr = function() use ($rest) { return $rest; };
  }
  public function first(){ return $this->car; } 
  public function rest(){ return $this->cdr(); } 
  public function filter($predicate){
    $next = $this;
    while(!$predicate($next->first())){
      $next = $next->rest();
    }
    $cell = new Cell($next->first(), null);
    $cell->cdr = function() use ($next, $predicate) {
      return $next->rest()->filter($predicate);
    };
    return $cell;
  }

 public function take($N){
    assert($N > 0);
    $cell = new Cell($this->first(), null);
    if($N == 1) return $cell;
    $that = $this;
    $cell->cdr = function() use ($that, $N) { return $that->rest()->take($N-1); };
    return $cell;
  }

  public function __toString(){
    $str = "(";
    $start = true;
    $next = $this;
    while($next != null){
      if($start == false) $str=$str." ";
      $start = false;
      $str = $str.$next->first();
      $next = $next->rest();
    }
    return $str.")";
  }

  public static function fromTransition($init, $transition){
    $cell = new Cell($init, null);
    $cell->cdr = function() use ($init, $transition){ 
      return Cell::fromTransition($transition($init), $transition);
    };  
    return $cell;
  } 

  public static function sieve($input, $paramPredicate){
    $x = $input->first();
    $cell = new Cell($x,null);
    $cell->cdr = function() use ($input, $paramPredicate, $x){
      return Cell::sieve(
        $input->rest()->filter(
          function($n) use ($paramPredicate, $x){
            return $paramPredicate($n, $x);}), 
        $paramPredicate); };
    return $cell;
  }
 
  // necessary boiler-plate so closure data member $cdr can be called as method
  public function __call($method, $args){               // lambda
    return call_user_func_array($this->$method,$args);  // don't forget 'return'
  }
} 

$numPrimes = (int) $argv[1];
$from2 = Cell::fromTransition(2,function($n){ return $n+1; });
$primes = Cell::sieve($from2, function($n,$x){ return $n % $x != 0; });
echo $primes->take($numPrimes).PHP_EOL;

?>
