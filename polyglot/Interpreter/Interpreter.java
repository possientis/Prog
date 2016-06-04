// Interpreter Design Pattern
import java.util.*;
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
  public static Exp Lit(String literal){ return new Lit(literal); }
  public static Exp And(Exp left, Exp right){ return new And(left, right); }
  public static Exp Or(Exp left, Exp right){ return new Or(left, right); }
  public static Exp Many(Exp regex){ return new Many(regex); }
  // instance interface
  @Override public abstract String toString();
  // Given a string, this method returns 'the' list of all prefixes of the string
  // which belong to the language of the regular expression object. Of course,
  // such a list in only unique up to the order of its elements
  public abstract List<String> interpret(String input);
  public boolean recognize(String input){ 
    return this.interpret(input).contains(input);
  }
}

class Lit extends Exp {

  private final String literal;
  protected Lit(String literal){ this.literal = literal; }

  @Override
  public String toString(){ return literal; }

  @Override
  public List<String> interpret(String input){
    List<String> result = new ArrayList<>();
    if (input.startsWith(literal)){ // literal is a prefix of input
      result.add(literal);
    }
    return result;
  }
} 

class And extends Exp {
  private final Exp left;
  private final Exp right;
  protected And(Exp left, Exp right){ this.left = left; this.right = right; }

  @Override
  public String toString(){ return "" + left + right; }

  @Override
  public List<String> interpret(String input){
    List<String> result = new ArrayList<>();
    List<String> leftList = left.interpret(input);
    for(String s1:leftList){
      String remainder = input.substring(s1.length());
      List<String> rightList = right.interpret(remainder);
      for(String s2:rightList){
        result.add(s1 + s2);
      }
    }
    return result;
  }
}

class Or extends Exp{
  private final Exp left;
  private final Exp right;
  protected Or(Exp left, Exp right){ this.left = left; this.right = right; }

  @Override
  public String toString(){ return "(" + left + "|" + right + ")"; }

  @Override
  public List<String> interpret(String input){
    List<String> result = left.interpret(input);
    List<String> rightList = right.interpret(input);
    for(String s:rightList){
      result.add(s);
    }
    return result;
  }
}

class Many extends Exp {
  private final Exp regex;
  protected Many(Exp regex){ this.regex = regex; }

  @Override
  public String toString(){ return "(" + regex + ")*"; }

  @Override
  public List<String> interpret(String input){
    List<String> result = new ArrayList<>();
    result.add(""); // forall r:Exp, "" belongs to L(r*)
    List<String> leftList = regex.interpret(input);
    for(String s1:leftList){
      if(!s1.isEmpty()){
        String remainder = input.substring(s1.length());
        List<String> rightList = this.interpret(remainder); // recursive call
        for(String s2:rightList){
          result.add(s1 + s2);
        }
      }
    }
    return result;
  }
}


public class Interpreter {
  public static void main(String[] args){
    Exp a = Exp.Lit("a");
    Exp b = Exp.Lit("b");
    Exp c = Exp.Lit("c");

    Exp aa = Exp.And(a, Exp.Many(a)); // one or more 'a'
    Exp bb = Exp.And(b, Exp.Many(b)); // one or more 'b'
    Exp cc = Exp.And(c, Exp.Many(c)); // one or more 'c'

    Exp regex = Exp.Many(Exp.And(Exp.Or(aa,bb),cc));
    String string = "acbbccaaacccbbbbaaaaaccccc";
    
    System.out.println("regex = " + regex);
    System.out.println("string = \"" + string + "\"");
    System.out.println("The recognized prefixes are:");
    List<String> result = new ArrayList<>();
    for(int i = 0; i <= string.length(); ++i){
      String test = string.substring(0,i);
      if(regex.recognize(test)){
        result.add("\"" + test + "\"");
      }
    }
    System.out.println(result);
  }
}




