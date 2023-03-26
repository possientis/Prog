<?php
// Interpreter Design Pattern

// from the Gang of Four book:
// "If a particular kind of problem occurs often enough, then it might be
// worthwhile to express instances of the problem as sentences in a simple
// language. Then you can build an interpreter that solves the problem by 
// interpreting these sentences. For example, searching for strings that 
// match a pattern is a common problem. Regular expressions are a standard 
// language for specifying patterns of strings. Rather than building custom 
// algorithms to match each pattern against strings, search algorithms could 
// interpret a regular expression that specifies a set of strings to match."

// Each regular expression r has an associated language L(r) (which is a set
// of strings) defined by the recursion:
//
//  - r = Lit(s)        -> L(r) = {s}
//  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
//  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
//  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
//
//  where given A,B sets of strings the product A.B is defined as the set of 
//  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
//  A^0 = {""} and A^1 = A. 
//
// Given a regular expression r and a string s, many reasonable questions 
// can be asked in relation to r and s. When using the command 'grep', the
// question being asked is whether there exist a substring s' of s which
// belongs to the language of r. One of the first questions of interest is
// of course whether s itself belongs to L(r).

abstract class Exp {
  // static factory methods
  public static function Lit($literal){
    return new Lit($literal);
  }
  public static function Conj($left, $right){
    return new Conj($left, $right);
  }
  public static function Disj($left, $right){
    return new Disj($left, $right);
  }
  public static function Many($regex){
    return new Many($regex);
  }
  // instance interface
  public abstract function __toString();
  // Given a string, this method returns 'the' list of all prefixes of the string
  // which belong to the language of the regular expression object. Of course,
  // such a list in only unique up to the order of its elements
  public abstract function interpret($input);
  public function recognize($input){
    return in_array($input, $this->interpret($input));  // java contains
  }
}

class Lit extends Exp {
  private $literal;
  protected function __construct($literal){
    $this->literal = $literal;
  }
  public function __toString(){ return $this->literal; }
  public function interpret($input){
    if(strncmp($input, $this->literal, strlen($this->literal)) == 0){
      return [$this->literal];
    } else {
      return [];
    }
  }
}

class Conj extends Exp {  // 'And' is a keyword
  private $left;
  private $right;
  protected function __construct($left, $right){
    $this->left = $left;
    $this->right = $right;
  }
  public function __toString(){
    return $this->left.$this->right;  // php string concatenation 
  }
  public function interpret($input){
    $result = [];
    $leftList = $this->left->interpret($input);
    foreach($leftList as $s1){
      $remainder = substr($input, strlen($s1));
      $rightList = $this->right->interpret($remainder);
      foreach($rightList as $s2){
        $result[] = $s1.$s2;         // php string concatenation
      }
    }
    return $result;
  }
}

class Disj extends Exp {  // 'Or' is a keyword
  private $left;
  private $right;
  protected function __construct($left, $right){
    $this->left = $left;
    $this->right = $right;
  }
  public function __toString(){
    return "(".$this->left."|".$this->right.")";  // php string concatenation 
  }
  public function interpret($input){
    $result = $this->left->interpret($input);
    $rightList = $this->right->interpret($input);
    foreach($rightList as $s){
      $result[] = $s;
    }
    return $result;
  }
}

class Many extends Exp {
  private $regex;
  protected function __construct($regex){ $this->regex = $regex; }
  public function __toString(){ return "(".$this->regex.")*"; }
  public function interpret($input){
    $result = [0 => ""];
    $leftList = $this->regex->interpret($input);
    foreach($leftList as $s1){
      if(!empty($s1)){
        $remainder = substr($input, strlen($s1));
        $rightList = $this->interpret($remainder);  // recursive call
        foreach($rightList as $s2){
          $result[] = $s1.$s2;            // php string concatenation
        }
      }
    }
    return $result;
  }
}

$a = Exp::Lit("a");
$b = Exp::Lit("b");
$c = Exp::Lit("c");

$aa = Exp::Conj($a, Exp::Many($a));   // one or more 'a'
$bb = Exp::Conj($b, Exp::Many($b));   // one or more 'b'
$cc = Exp::Conj($c, Exp::Many($c));   // one or more 'c'

$regex = Exp::Many(Exp::Conj(Exp::Disj($aa, $bb), $cc));
$string = "acbbccaaacccbbbbaaaaaccccc";

echo "regex = ".$regex."\n";
echo "string = \"".$string."\"\n";
echo "The recognized prefixes are:\n";
$result = [];
for($i = 0; $i <= strlen($string); ++$i){
  $test = substr($string,0,$i);
  if($regex->recognize($test)){
    $result[] = "\"".$test."\"";
  }
}

// printing things nicely
echo "[";
$start = true;
foreach($result as $s){
  if($start){
    $start = false;
  } else {
    echo ", ";
  }
  echo $s;
}
echo "]\n";






?>
