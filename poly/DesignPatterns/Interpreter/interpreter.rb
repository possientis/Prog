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
  def self.Lit(literal) 
    return Lit.new(literal) 
  end
  def self.And(left, right) 
    return And.new(left, right) 
  end
  def self.Or(left, right) 
    return Or.new(left, right) 
  end
  def self.Many(regex)
    return Many.new(regex)
  end
  # instance interface
  def to_s()
    raise NotImplementedError.new "Exp::to_s is not implemented"
  end
  def interpret(input)
    raise NotImplementedError.new "Exp::interpret is not implemented"
  end
  def recognize(input)
    return interpret(input).include? input 
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
    leftList.each do |s1|
      remainder = input[s1.length..-1]
      rightList = @right.interpret(remainder)
      rightList.each do |s2|
        result.push s1 + s2
      end 
    end 
    return result
  end
end

class Or < Exp
  def initialize(left, right)
    @left = left 
    @right = right 
  end
  def to_s()
    return "(#{@left}|#{@right})"
  end
  def interpret(input)
    return @left.interpret(input) + @right.interpret(input)
  end
end

class Many < Exp
  def initialize(regex)
    @regex = regex
  end
  def to_s()
    return "(#{@regex})*"
  end
  def interpret(input)
    result = [""]
    leftList = @regex.interpret(input)
    leftList.each do |s1|
      if !s1.empty? then  # s1 is not the empty string
        remainder = input[s1.length..-1]  # substring
        rightList = interpret(remainder)  # recursive call
        rightList.each do |s2|
          result.push s1 + s2   # java add
        end 
      end
    end 
    return result
  end
end

   
a = Exp.Lit("a")
b = Exp.Lit("b")
c = Exp.Lit("c")

aa = Exp.And(a, Exp.Many(a))  # one or more 'a'
bb = Exp.And(b, Exp.Many(b))  # one or more 'b'
cc = Exp.And(c, Exp.Many(c))  # one or more 'c'

regex = Exp.Many(Exp.And(Exp.Or(aa, bb), cc))
string = "acbbccaaacccbbbbaaaaaccccc"

puts "regex = #{regex}"
puts "string = \"#{string}\""
puts "The recognized prefixes are:"

result = []
(0..string.length).each do |i|
  test = string[0...i]    # '...' -> exclude i (python semantics)
  if regex.recognize(test) then
    result.push "\"#{test}\""   # adding array
  end
end

# printing result nicely
print "["
start = true
result.each do |s|
  if start then
    start = false
  else
    print ", "
  end
  print s
end
print "]\n"













