import Number
from Bench_Abstract import *

class Bench_Number(Bench_Abstract):

    def run(self):
        logMessage("Number benchmark running ...")

        runAll = True

        benchFromBytes();
        benchToBytes();
        benchAdd();
        benchMul();
        benchToString();
        benchRandom();

        if runAll:
            benchZERO();
            benchONE();
            benchSignum();
            benchCompareTo();
            benchHashCode();
            benchNumberEquals();  
            benchFromBigInteger();
            benchToBigInteger();
            benchBitLength();
 

def benchZERO():
    def test1():
        x = Number.ZERO;
    def test2():
        x = 0
    benchmark(test1, "ZERO", 1000000)
    benchmark(test2, "ZERO*", 1000000)

def benchONE():
    def test1():
        x = Number.ONE;
    def test2():
        x = 1
    benchmark(test1, "ONE", 1000000)
    benchmark(test2, "ONE*", 1000000)

def benchFromBytes():
    bs = getRandomBytes(32)
    def test1():
        Number.fromBytes(1, bs)
        Number.fromBytes(-1, bs)
    def test2():
        int.from_bytes(bs, byteorder='big', signed=False)
        -int.from_bytes(bs, byteorder='big', signed=False)

    benchmark(test1, "fromBytes (10k)", 10000)
    benchmark(test2, "fromBytes* (10k)", 10000)


def benchToBytes(): pass # TODO
def benchAdd(): pass # TODO
def benchMul(): pass # TODO
def benchToString(): pass # TODO
def benchRandom(): pass # TODO
def benchSignum(): pass # TODO
def benchCompareTo(): pass # TODO
def benchHashCode(): pass # TODO
def benchNumberEquals(): pass # TODO
def benchFromBigInteger(): pass # TODO
def benchToBigInteger(): pass # TODO
def benchBitLength(): pass # TODO

bench = Bench_Number()
bench.run()




