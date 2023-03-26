# We did not implement memoization in the thunk. We initially forgot,
# then realized it had no beneficial impact in the Scheme implementation

import sys  # sys.argv, importing command line arguments
sys.setrecursionlimit(10000)


# quick and dirty implementation of infinite streams
# (which can be finite). We have not defined the empty stream.
class Cell:
    def __init__(self,first, rest):
        self.car = first
        self.cdr = lambda : rest
    @property
    def first(self):
        return self.car
    @property
    def rest(self):
        return self.cdr()
    def take(self, N):
        assert N > 0
        cell = Cell(self.first, None)
        if N == 1: return cell
        func = self.cdr     # avoiding capture of 'self' in lambda, just in case..
        cell.cdr = lambda : func().take(N-1)
        return cell
    def __str__(self):  # pretty print, use __repr__ for unambiguous string rep
        out = "("
        start = True
        current = self
        while current != None:
            if not start: 
                out += " " 
            else : 
                start = False
            out += str(current.first)
            current = current.rest  # should be None at some point if finite stream
        return out + ")"
    def filter(self, predicate):
        current = self
        while not predicate(current.first):
            current = current.rest
        cell = Cell(current.first, None)
        cell.cdr = lambda : current.rest.filter(predicate)
        return cell
    def fromTransition(init,transition):    # static member
        cell = Cell(init, None)
        cell.cdr = lambda : Cell.fromTransition(transition(init), transition)
        return cell
    def sieve(stream, paramPredicate):       # static member
        x = stream.first
        cell = Cell(x, None)
        cell.cdr = lambda : Cell.sieve(
                stream.rest.filter(lambda n: paramPredicate(n,x)), paramPredicate
                )
        return cell
        

numPrimes = int(sys.argv[1])
from2 = Cell.fromTransition(2, lambda n: n+1)
primes = Cell.sieve(from2, lambda n,x: n% x != 0)
print(primes.take(numPrimes))



