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
# design pattern can be successfully applied, allowing the implementation 
# of the ATM machine to forget about all those different services and 
# the details of how to convert an amount of cash into a set of notes.


# Our ATM machine only need to worry about the head of the chain of
# services, which it maintains as an internal data member. This machine
# has the ability to provide a set of bank notes from a desired amount
class ATMMachine:
    # private data member representing the head of the chain of handlers
    def __init__(self):
        self._handler = RequestHandler.getHandlingChain()
    # main functionality
    def getAmount(self, amount):
        print("ATM machine: requesting amount of $" + str(amount))
        return self._handler.handleRequest(amount)   # delegates request to chain

# This is the base class, uniting all request handlers into a common
# interface. This class in normally abstract (the whole point of the
# design pattern is dealing with multiple types of request).
class RequestHandler:
    def __init__(self, nextHandler):
        self._next = nextHandler

    # setting up the chain of responsibility. In our case, the request
    # handler responsible of the delivery of $50 notes will intervene
    # first, then pass on request to its successor
    def getHandlingChain(): # static method
        handler = RequestHandlerForFive(None)
        handler = RequestHandlerForTen(handler)
        handler = RequestHandlerForTwenty(handler)
        handler = RequestHandlerForFifty(handler)
        return handler

    # This is the main method of the class. It is often an abstract
    # method as the diffeent types of request handlers may have little
    # in common. In our case, all request handlers are similar and only
    # differ in the specific denomination of the bank note they deliver.
    # Such denominations are encoded in a virtual method.
    def handleRequest(self, amount):
        if amount < 0 : raise Exception("Illegal Argument")
        if amount == 0 : return []
        if amount % 5 != 0 :    # modulo
            raise Exception("Amount should be multiple of 5")

        # handleRequest logic is the same across all request handlers
        # in our case. However, this logic is parameterized by denomination
        # This is a case of mini-template method design pattern.
        denom = self.denomination()
        value = denom.value
        addSingleNote = False   # whether handler gives away note

        if amount >= value :
            noteList = self.handleRequest(amount - value)   # recursive call
            addSingleNote = True                            # handler give note?
        else:
            if self._next != None:
                noteList = self._next.handleRequest(amount) # passing on request
            else:
                raise Exception("Illegal State")            # chain badly set up

        # set of bank notes obtained by a mixture of recursive call and 
        # delegation of request to the next handler on the chain. We 
        # should not forget to add a single note if required.
        if addSingleNote: noteList.append(denom)

        return noteList

    def denomination(self):
        raise NotImplementedError


# delivers %50 notes
class RequestHandlerForFifty(RequestHandler):
    def __init__(self, nextHandler):
        RequestHandler.__init__(self, nextHandler)
    def denomination(self): return Fifty()

# delivers %20 notes
class RequestHandlerForTwenty(RequestHandler):
    def __init__(self, nextHandler):
        RequestHandler.__init__(self, nextHandler)
    def denomination(self): return Twenty()

# delivers %10 notes
class RequestHandlerForTen(RequestHandler):
    def __init__(self, nextHandler):
        RequestHandler.__init__(self, nextHandler)
    def denomination(self): return Ten()

# delivers %5 notes
class RequestHandlerForFive(RequestHandler):
    def __init__(self, nextHandler):
        RequestHandler.__init__(self, nextHandler)
    def denomination(self): return Five()

class BankNote:
    @property
    def value(self): raise NotImplementedError
    def __str__(self): return str(self.value)
    def toInt(seq): return list (map(lambda x: x.value, seq))

class Five(BankNote):
    @property
    def value(self): return 5

class Ten(BankNote):
    @property
    def value(self): return 10 

class Twenty(BankNote):
    @property
    def value(self): return 20

class Fifty(BankNote):
    @property
    def value(self): return 50

# main
atm = ATMMachine()
noteList = atm.getAmount(235)
print("The notes handed out by the ATM machine are:")
print(BankNote.toInt(noteList))







 






