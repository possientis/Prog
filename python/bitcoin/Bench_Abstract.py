import random
import sys
import time

class Bench_Abstract(object):

    randGen = random.SystemRandom() 

    def run():
        raise NotImplementedError("Bench_Abstract: run is abstract")


def getRandomBytes(numBytes):
    value = Bench_Abstract.randGen.getrandbits(numBytes*8)
    return value.to_bytes(numBytes, byteorder='big', signed=False)


def logMessage(message):
    sys.stderr.write(message+"\n")

def benchmark(callbk, name, iterations):

    start = time.time()

    for i in range(0, iterations):
        callbk()

    end = time.time()

    diff = (end - start)

    logMessage(
        "Benchmark: %s, %d iterations ran in %.3f seconds" % 
        (name, iterations, diff)
    )


