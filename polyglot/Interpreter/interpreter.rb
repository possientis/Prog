# Interpreter Design Pattern

# from the Gang of Four book:
# "If a particular kind of problem occurs often enough, then it might be
# worthwhile to express instances of the problem as sentences in a simple
# language. Then you can build an interpreter that solves the problem by 
# interpreting these sentences. For example, searching for strings that 
# match a pattern is a common problem. Regular expressions are a standard 
# language for specifying patterns of strings. Rather than building custom 
# algorithms to match each pattern against strings, search algorithms could 
# interpret a regular expression that specifies a set of strings to match."

# Each regular expression r has an associated language L(r) (which is a set
# of strings) defined by the recursion:
#
#  - r = Lit(s)        -> L(r) = {s}
#  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
#  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
#  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
#
#  where given A,B sets of strings the product A.B is defined as the set of 
#  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
#  A^0 = {""} and A^1 = A. 
#
# Given a regular expression r and a string s, many reasonable questions 
# can be asked in relation to r and s. When using the command 'grep', the
# question being asked is whether there exist a substring s' of s which
# belongs to the language of r. One of the first questions of interest is
# of course whether s itself belongs to L(r).

class Exp
  # static interface
  # TODO
  # instance interface
  def to_s()
    raise NotImplementedError.new "Exp::to_s is not implemented"
  end
  def interpret(input)
    raise NotImplementedError.new "Exp::interpret is not implemented"
  end
  def recognize(input)
    return false  # TODO
  end
end

class Lit < Exp
  def initialize(literal)
    @literal = literal
  end
  def to_s()
    return @literal
  end
  def interpret(input)
    if input.start_with?(@literal) then # literal is a prefix of input
      return [@literal]
    else
      return []
    end
  end
end

class And < Exp
  def initialize(left, right)
    @left = left 
    @right = right 
  end
  def to_s()
    return "#{@left}#{@right}"
  end
  def interpret(input)
    result = []
    leftList = @left.interpret(input)
    leftList.each {|s1|
      remainder = input[s1.length..-1]
      rightList = @right.interpret(remainder)
      rightList.each { |s2|
        result[result.length] = s1 + s2
      }
    }
    return result
  end
end



x = And.new(Lit.new("a"), Lit.new("b"))
puts x.interpret("Abcdef")


