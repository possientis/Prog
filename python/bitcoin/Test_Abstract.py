import random

class Test_Abstract(object):

    randGen = random.SystemRandom()

    def run():
        raise NotImplementedError

    def getRandomBytes(numBytes):
        value = Test_Abstract.randGen.getrandbits(numBytes*8)
        return value.to_bytes(numBytes, byteorder='big', signed=False)
    
    def logMessage(message):
        pass

x = Test_Abstract()

bs = Test_Abstract.getRandomBytes(32)
print(bs)
print(len(bs))

