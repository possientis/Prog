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
//
//
//
//

abstract class Exp {
  // static factory methods
  public static Exp Lit(String literal){ return new Lit(literal); }
  public static Exp And(Exp left, Exp right){ return new And(left, right); }
  public static Exp Or(Exp left, Exp right){ return new Or(left, right); }
  public static Exp Many(Exp regex){ return new Many(regex); }
  // instance interface
  @Override public abstract String toString();
  public abstract List<String> interpret(String input);
}

class Lit extends Exp {
  private final String literal;
  protected Lit(String literal){ this.literal = literal; }
  @Override
  public String toString(){ return "Lit(" + literal + ")"; }
  @Override
  public List<String> interpret(String input){
    return null;
  }
} 

class And extends Exp {
  private final Exp left;
  private final Exp right;
  protected And(Exp left, Exp right){ this.left = left; this.right = right; }
  @Override
  public String toString(){ return "And(" + left + ", " + right + ")"; }
  @Override
  public List<String> interpret(String input){
    return null;
  }
}

class Or extends Exp{
  private final Exp left;
  private final Exp right;
  protected Or(Exp left, Exp right){ this.left = left; this.right = right; }
  @Override
  public String toString(){ return "Or(" + left + ", " + right + ")"; }
  @Override
  public List<String> interpret(String input){
    return null;
  }
}



class Many extends Exp {
  private final Exp regex;
  protected Many(Exp regex){ this.regex = regex; }
  @Override
  public String toString(){ return "Many(" + regex + ")"; }
  @Override
  public List<String> interpret(String input){
    return null;
  }
}



public class Interpreter {
  public static void main(String[] args){
    Exp r1 = Exp.Lit("hello");
    Exp r2 = Exp.Lit("world");
    Exp r3 = Exp.And(r1, r2);
    Exp r4 = Exp.Or(r1, r3);
    Exp r5 = Exp.Many(r4);
    System.out.println(r5);
  }
}




