# it all works, there is no quirks relating to the capture of 'this' or 'self'
# in lambda expressions, unlike JavaScript, but performance is disappointing
# compared to JavaScript or Scheme. Still a lot better than PHP.

# We did not implement memoization in the thunk. We initially forgot,
# then realized it had no beneficial impact in the Scheme implementation
#
# there is no assert in ruby
class AssertionError < RuntimeError
end
def assert(condition)
  if !condition then
    raise AssertionError
  end
end


# quick and dirty implementation of infinite streams
# (which can be finite). We have not defined the empty stream.
class Cell
  def initialize(first, rest)
    @car = first
    @cdr = lambda { rest }
  end
  attr_reader :first, :rest
  attr_writer :cdr  # needed to overwrite (encapsulated field)
  def first()
   return @car
  end
  def rest()
   return @cdr.call() # don't forget to use 'call' on function objects
  end 
  def take(n)
    assert(n > 0)
    cell = Cell.new(first,nil)
    if n == 1 then return cell end
    cell.cdr = lambda { rest.take(n - 1) }
    return cell
  end
  def to_s()
    str = "("
    start = true
    current = self
    while  current != nil do
      if !start then str += " " else start = false end
      str += current.first.to_s
      current = current.rest  # should be nil at some point if finite stream
    end
    return str + ")"
  end
  def filter(predicate)
    current = self
    while !predicate.call(current.first) do
      current = current.rest
    end
    cell = Cell.new(current.first, nil)
    cell.cdr = lambda { current.rest.filter(predicate) }
    return cell # return seems optional
  end

  def self.fromTransition(init, transition) # static member
    cell = Cell.new(init, nil)
    cell.cdr = lambda { fromTransition(transition.call(init), transition) }
    return cell # return seems optional
  end

  def self.sieve(input, paramPredicate)     # static member
    x = input.first
    cell = Cell.new(x,nil)
    cell.cdr = lambda { 
      sieve(
        input.rest.filter(lambda {|n| paramPredicate.call(n,x)}), 
        paramPredicate
      )
    }
    return cell
  end
end

numPrimes =  ARGV[0].to_i   # retrieving command line argument 
from2 = Cell.fromTransition(2, lambda { |n| n + 1 })
primes = Cell.sieve(from2, lambda { |n,x| n % x != 0 })
puts primes.take(numPrimes)






