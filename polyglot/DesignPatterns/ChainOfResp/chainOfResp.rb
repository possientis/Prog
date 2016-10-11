# Chain of Responsibility Design Pattern

# The Chain Of Responsibility design pattern is meant to decouple
# clients (which may have various requests) from request handlers
# which may be of different types. Rather than forcing a client
# to have the precise knowledge of which request handler is able
# to deal with which type of request, the Chain of Responsibility
# design pattern creates a common base interface to all request
# handlers, and unites them into a single linked list (a 'chain').
# Now the client only needs to know the head of the chain, to
# which it sends all of its requests. Each request handler, apart
# from maintaining a link to a 'successor', fundamentally has
# a 'handleRequest' method which now accepts all types of request.
# However, when faced with a request which it cannot fulfill, a 
# request handler will pass on the request to its successor. 
# Provided the chain of request handlers is properly set up, all
# requests should be handled appropriately.
#
# Note that this pattern can be generalized from 'chains' to non
# linear structure between objects, such as trees. One can imagine
# a network of request handlers, which are either dealing with 
# request themselves, or passing requests to other (linked) 
# request handlers
#
# This coding exercise is meant to provide a simulation of an ATM
# machine. As a server, the machine is able to provide a service
# 'getAmount' to an external client which consists in the delivery
# of the appropriate set of bank notes which corresponds to a 
# desired amount. As a client, the ATM machine relies on various
# request handlers, namely those which are specialized in the delivery
# of specific bank notes. So the machine relies on a service for the 
# delivery of $5 notes, another service for the delivery of $10 notes
# and so forth. This is a case where the Chain of Responsibility 
# design pattern can be succesfully applied, allowing the implementation 
# of the ATM machine to forget about all those different services and 
# the details of how to convert an amount of cash into a set of notes.


# Our ATM machine only need to worry about the head of the chain of
# services, which it maintains as an internal data member. This machine
# has the ability to provide a set of bank notes from a desired amount
class ATMMachine
  # private data member representing the head of the chain of handlers
  def initialize()
    @handler = RequestHandler.getHandlingChain()
  end
  # main functionality
  def getAmount(amount)
    puts "ATM machine: requesting amount of $#{amount}"
    return @handler.handleRequest(amount) # delegates request to chain
  end
end

# This is the base class, uniting all request handlers into a common
# interface. This class in normally abstract (the whole point of the
# design pattern is dealing with multiple types of request).
class RequestHandler
  def initialize(nextHandler)
    @next = nextHandler
  end
 
  # setting up the chain of responsibility. In our case, the request
  # handler responsible of the delivery of $50 notes will intervene
  # first, then pass on request to its successor
  def self.getHandlingChain() # static method
    handler = RequestHandlerForFive.new(nil)
    handler = RequestHandlerForTen.new(handler)
    handler = RequestHandlerForTwenty.new(handler)
    handler = RequestHandlerForFifty.new(handler)
    return handler
  end
  # This is the main method of the class. It is often an abstract
  # method as the diffeent types of request handlers may have little
  # in common. In our case, all request handlers are similar and only
  # differ in the specific denomination of the bank note they deliver.
  # Such denominations are encoded in a virtual method.
  def handleRequest(amount)
    if(amount < 0)  then raise Exception.new "Illegal Argument" end
    if(amount == 0) then return [] end
    if(amount % 5 != 0) then  # modulo
      raise Exception.new "Amount should be multiple of 5"
    end

    # handleRequest logic is the same across all request handlers
    # in our case. However, this logic is parameterized by denomination
    # This is a case of mini-template method design pattern.
    denom = denomination()
    value = denom.value
    addSingleNote = false # whether handler gives away note

    if(amount >= value) then
      list = handleRequest(amount - value)    # recursive call
      addSingleNote = true                    # handler should give note
    else
      if(@next != nil) then
        list = @next.handleRequest(amount)    # passing on request
      else
        raise Exception.new "Illegal State"   # chain badly set up
      end
    end
    # set of bank notes obtained by a mixture of recursive call and 
    # delegation of request to the next handler on the chain. We 
    # should not forget to add a single note if required.
    if addSingleNote then list.push(denom) end 

    return list
  end

  def denomination()  # abstract
    raise NotImplementedError.new 
  end
end

# delivers $50 notes
class RequestHandlerForFifty < RequestHandler
  def initialize(nextHandler) super(nextHandler) end
  def denomination() return Fifty.new end
end

# delivers $20 notes
class RequestHandlerForTwenty < RequestHandler
  def initialize(nextHandler) super(nextHandler) end
  def denomination() return Twenty.new end
end

# delivers $10 notes
class RequestHandlerForTen < RequestHandler
  def initialize(nextHandler) super(nextHandler) end
  def denomination() return Ten.new end
end

# delivers $5 notes
class RequestHandlerForFive < RequestHandler
  def initialize(nextHandler) super(nextHandler) end
  def denomination() return Five.new end
end

class BankNote
  def value() raise NotImplementedError.new end
  def to_s() return value.to_s end
  def self.toInt(list) return list.map(&:value) end # possible lambda syntax
end

class Five < BankNote
  def value() return 5 end
end

class Ten < BankNote
  def value() return 10 end
end

class Twenty < BankNote
  def value() return 20 end
end

class Fifty < BankNote
  def value() return 50 end
end

#main
atm = ATMMachine.new
list = atm.getAmount(235)
puts "The notes handed out by the ATM machine are:"
print BankNote.toInt(list)
puts


