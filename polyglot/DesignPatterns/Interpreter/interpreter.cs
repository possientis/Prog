// Interpreter Design Pattern
using System;
using System.Collections.Generic;
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
  public static Exp Lit(string literal){ return new Lit(literal); }
  public static Exp And(Exp left, Exp right){ return new And(left, right); }
  public static Exp Or(Exp left, Exp right){ return new Or(left, right); }
  public static Exp Many(Exp regex){ return new Many(regex); }
  // instance interface
  public abstract override string ToString();
  // Given a string, this method returns 'the' list of all prefixes of the string
  // which belong to the language of the regular expression object. Of course,
  // such a list is only unique up to the order of its elements
  public abstract IList<string> Interpret(string input);
  public bool Recognize(string input){ 
    return this.Interpret(input).Contains(input);
  }
}

class Lit : Exp {
  private readonly string literal;
  public Lit(string literal){ this.literal = literal; }
  public override string ToString(){ return literal; }
  public override IList<string> Interpret(string input){
    IList<string> result = new List<string>();
    if(input.StartsWith(literal)){  // literal is a prefix of input
      result.Add(literal);
    }
    return result;
  }
}

class And : Exp {
  private readonly Exp left;
  private readonly Exp right;
  public And(Exp left, Exp right){ this.left = left; this.right = right; }
  public override string ToString(){ return "" + left + right; }
  public override IList<string> Interpret(string input){
    IList<string> result = new List<string>();
    IList<string> leftList = left.Interpret(input);
    foreach(string s1 in leftList){
      string remainder = input.Substring(s1.Length);
      IList<string> rightList = right.Interpret(remainder);
      foreach(string s2 in rightList){
        result.Add(s1 + s2);
      }
    }
    return result;
  }
}

class Or  : Exp {
  private readonly Exp left;
  private readonly Exp right;
  public Or(Exp left, Exp right){ this.left = left; this.right = right; }
  public override string ToString(){ return "(" + left + "|" + right + ")" ; }
  public override IList<string> Interpret(string input){
    IList<string> result = left.Interpret(input);
    IList<string> rightList = right.Interpret(input);
    foreach(string s in rightList){
      result.Add(s);
    }
    return result;
  }
}


class Many: Exp{
  private readonly Exp regex;
  public Many(Exp regex){ this.regex = regex; }
  public override string ToString(){ return "(" + regex + ")*"; }
  public override IList<string> Interpret(string input){
    IList<string> result = new List<string>();
    result.Add(""); // forall r:Exp, "" belongs to L(r*)
    IList<string> leftList = regex.Interpret(input);
    foreach(string s1 in leftList){
      if(!s1.Equals(String.Empty)){
        string remainder = input.Substring(s1.Length);
        IList<string> rightList = this.Interpret(remainder);  // recursive call
        foreach(string s2 in rightList){
          result.Add(s1 + s2);
        }
      }
    }
    return result;
  }
}


public class Interpreter {
  public static void Main(string[] args){
    Exp a = Exp.Lit("a");
    Exp b = Exp.Lit("b");
    Exp c = Exp.Lit("c");

    Exp aa = Exp.And(a, Exp.Many(a)); // one or more 'a'
    Exp bb = Exp.And(b, Exp.Many(b)); // one or more 'b'
    Exp cc = Exp.And(c, Exp.Many(c)); // one or more 'c'

    Exp regex = Exp.Many(Exp.And(Exp.Or(aa,bb),cc));
    string str = "acbbccaaacccbbbbaaaaaccccc";
    
    Console.WriteLine("regex = " + regex);
    Console.WriteLine("string = \"" + str + "\"");
    Console.WriteLine("The recognized prefixes are:");
    IList<string> result = new List<string>();
    for(int i = 0; i <= str.Length; ++i){
      string test = str.Substring(0,i);
      if(regex.Recognize(test)){
        result.Add("\"" + test + "\"");
      }
    }
    Print(result);
  }

  public static void Print(IList<string> list){
    bool start = true;
    Console.Write("[");
    foreach(string s in list){
      if(start){
        start = false;
      } else {
        Console.Write(", ");
      }
      Console.Write(s);
    }
    Console.WriteLine("]");
  }
}
