import random
import sys


class Test_Abstract(object):

    randGen = random.SystemRandom()

    def run():
        raise NotImplementedError


def getRandomBytes(numBytes):
    value = Test_Abstract.randGen.getrandbits(numBytes*8)
    return value.to_bytes(numBytes, byteorder='big', signed=False)
 
def logMessage(message):
    sys.stderr.write(message+"\n")

def checkEquals(left, right, message):
    if not left is None:
        if left != right:
            logMessage(message + ": checkEquals failure")
            logMessage("left = " + str(left))
            logMessage("right = " + str(right))
            sys.exit(1)
        # in case equals override is not symmetric
        if right != left:
            logMessage(message + ": checkEquals failure")
            logMessage("override of == method is not symmetric")
            logMessage("left == right is true while right == left is false")
            sys.exit(1)
    else:
        if not right is None:
            logMessage(message + ": checkEquals failure")
            logMessage("left is None, but right is not")
            sys.exit(1)

def checkNotNone(obj, message):
    if obj == None:
        logMessage(message + ": checkNotNone failure")
        sys.exit(1)

def checkCondition(cond, message):
    if not cond:
        logMessage(message + ":checkCondition failure")
        sys.exit(1)

def checkException(callbk, name, message):
    try:
        callbk()
        logMessage(message + ": checkException failure: no exception detected")
        sys.exit(1)

    except Exception as e:
        if type(e).__name__ != name:
            logMessage(message + ": checkException failure: wrong exception type")
            logMessage("Expected: " + name)
            logMessage("Actual: " + type(e).__name__)
            sys.exit(1)



