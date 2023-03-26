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

function Exp(){}
// static factory methods
Exp.Lit   = function(literal)     { return new Lit(literal);      }
Exp.And   = function(left, right) { return new And(left, right);  }
Exp.Or    = function(left, right) { return new Or(left, right);   }
Exp.Many  = function(regex)       { return new Many(regex);       }

// instance interface
Exp.prototype.toString = function(){ throw "Exp::toString is not implemented"; }
// Given a string, this method returns 'the' list of all prefixes of the string
// which belong to the language of the regular expression object. Of course,
// such a list in only unique up to the order of its elements
Exp.prototype.interpret = function(input){ 
  throw "Exp::interpret is not implemented"; 
}
Exp.prototype.recognize = function(input){
  return this.interpret(input).indexOf(input) != -1; 
}

function Lit(literal){ this.literal = literal; }
Lit.prototype = new Exp();  // = Object.create(Exp.prototype)
Lit.prototype.toString = function(){ return this.literal; }
Lit.prototype.interpret = function(input){
  if(input.startsWith(this.literal)){  // literal is a prefix of input
    return [this.literal]; // array literal
  } else {
    return [];        // empty list literal
  }
}

function And(left, right){ this.left = left; this.right = right; }
And.prototype = new Exp();  // = Object.create(Exp.prototype) 
And.prototype.toString = function(){ return this.left + this.right; } // concat
And.prototype.interpret = function(input){
  var result = []; 
  var leftList = this.left.interpret(input);
  for(var i = 0; i < leftList.length; ++i){ 
    var s1 = leftList[i];
    var remainder = input.substring(s1.length);
    var rightList = this.right.interpret(remainder);
    rightList.forEach(function(s2){
      result.push(s1 + s2);
    });
  }
  return result;
}

function Or(left, right){ this.left = left; this.right = right; }
Or.prototype = new Exp();  // = Object.create(Exp.prototype) 
Or.prototype.toString = function(){ 
  return "(" + this.left + "|" + this.right + ")"; } // concat, append
Or.prototype.interpret = function(input){
  // concatenation of two arrays using '+' did not seem to work here
  return  this.left.interpret(input).concat(this.right.interpret(input)); // append
}


function Many(regex){ this.regex = regex; }
Many.prototype = new Exp(); // = Object.create(Exp.prototype)
Many.prototype.toString = function(){ return "(" + this.regex + ")*"; }
Many.prototype.interpret = function(input){
  var result = [""];  // forall r:Exp, "" belongs to L(r*)
  var leftList = this.regex.interpret(input);
  for(var i = 0; i < leftList.length; ++i){
    var s1 = leftList[i];
    if(s1 !== ""){  // s1 is not the empty string
      var remainder = input.substring(s1.length);
      var rightList = this.interpret(remainder); // recursive call 
      rightList.forEach(function(s2){
        result.push(s1 + s2);
      });
    }
  }
  return result;
}
  
// main
a = Exp.Lit("a");
b = Exp.Lit("b");
c = Exp.Lit("c");

aa = Exp.And(a, Exp.Many(a)); // one or more 'a'
bb = Exp.And(b, Exp.Many(b)); // one or more 'b'
cc = Exp.And(c, Exp.Many(c)); // one or more 'c'

regex = Exp.Many(Exp.And(Exp.Or(aa,bb),cc));
string = "acbbccaaacccbbbbaaaaaccccc";

console.log("regex = " + regex);
console.log("string = \"" + string + "\"");
console.log("The recognized prefixes are:");

var result = [];
for(var i = 0; i <= string.length; ++i){
  var test = string.substring(0,i);
  if(regex.recognize(test)){
    result.push("\"" + test + "\"");
  }
}

// nice display
var str = "[";
var start = true;
for(var i = 0; i < result.length; ++i){
  if(start){
    start = false
  } else {
    str += ", ";
  }
  str += result[i];
}
str+="]";
console.log(str);
















