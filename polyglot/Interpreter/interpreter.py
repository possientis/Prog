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


# There is no need to create static factory methods in python, as the
# usual constructors have exactly the desired syntax
class Exp():
    # instance interface
    def __str__(self):
        raise NotImplementedError("Exp::__str__ is not implemented")
    def interpret(self, input):
        raise NotImplementedError("Exp::interpret is not implemented")
    def recognize(self, input):
        return input in self.interpret(input)


class Lit(Exp):
    def __init__(self, literal):
        self._literal = literal
    def __str__(self):
        return self._literal
    def interpret(self, input):
        if input.startswith(self._literal): # _literal is a prefix of input
            return [self._literal]
        else:
            return []

class And(Exp):
    def __init__(self, left, right):
        self._left = left
        self._right = right
    def __str__(self):
        return str(self._left) + str(self._right)
    def interpret(self, input):
        result = []
        leftList = self._left.interpret(input)
        for s1 in leftList:
            remainder = input[len(s1):]
            rightList = self._right.interpret(remainder)
            for s2 in rightList:
                result.append(s1 + s2)
        return result

class Or(Exp):
    def __init__(self, left, right):
        self._left = left
        self._right = right
    def __str__(self):
        return "(" + str(self._left) + "|" + str(self._right) + ")"
    def interpret(self, input):
        return self._left.interpret(input) + self._right.interpret(input)


class Many(Exp):
    def __init__(self, regex):
        self._regex = regex
    def __str__(self):
        return "(" + str(self._regex) + ")*"
    def interpret(self, input):
        result = [""]
        leftList = self._regex.interpret(input)
        for s1 in leftList:
            if s1:  # s1 is not the empty string
                remainder = input[len(s1):]
                rightList = self.interpret(remainder)   # recursive call
                for s2 in rightList:
                    result.append(s1 + s2)
        return result


a = Lit("a")
b = Lit("b")
c = Lit("c")

aa = And(a, Many(a))    # one or more 'a'
bb = And(b, Many(b))    # one or more 'b'
cc = And(c, Many(c))    # one or more 'c'

regex = Many(And(Or(aa,bb),cc))
string = "acbbccaaacccbbbbaaaaaccccc"

print("regex = " + str(regex))
print("string = \"" + string + "\"")
print("The recognized prefixes are:")
result = []
for i in range(0,len(string)):
    test = string[0:i]
    if regex.recognize(test):
        result.append("\"" + test + "\"")
start = True
print("[", end = "")
for test in result:
    if start:
        start = False
    else:
        print(", ", end = "")
    print(test, end = "")
print("]")




    






