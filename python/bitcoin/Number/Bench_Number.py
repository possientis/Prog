import Number
from Bench_Abstract import *

class Bench_Number(Bench_Abstract):

    def run(self):
        logMessage("Number benchmark running ...")

        runAll = True

        benchFromBytes()
        benchToBytes()
        benchAdd()
        benchMul()
        benchNegate()
        benchToString()
        benchRandom()

        if runAll:
            benchZERO()
            benchONE()
            benchSign()
            benchCompareTo()
            benchHashCode()
            benchNumberEquals()  
            benchFromBigInteger()
            benchToInt()
            benchBitLength()
 

def benchZERO():
    def test1():
        x = Number.ZERO
    def test2():
        x = 0
    benchmark(test1, "ZERO", 1000000)
    benchmark(test2, "ZERO*", 1000000)

def benchONE():
    def test1():
        x = Number.ONE
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

    benchmark(test1, "fromBytes (10k)", 10000)  # 1 million too slow
    benchmark(test2, "fromBytes* (10k)", 10000) # 1 million too slow


def benchToBytes():
    x = Number.random(256)
    y = -x
    n = int(x)
    m = int(y)
    def test1():
        x.toBytes(32)
        y.toBytes(32)
    def test2():
        n.to_bytes(32, byteorder='big', signed=False)
        m.to_bytes(33, byteorder='big', signed=True)
    benchmark(test1, "toBytes (10k)", 10000)    # 1 million too slow
    benchmark(test2, "toBytes* (10k)", 10000)   # 1 million too slow

def benchAdd():
    x = Number.random(256)
    y = -Number.random(256)
    n = int(x)
    m = int(y)
    def test1():
        x + y
        y + x
    def test2():
        n + m
        m + n
    benchmark(test1, "add (10k)", 10000)
    benchmark(test2, "add* (10k)", 10000)

def benchMul():
    x = Number.random(256)
    y = -Number.random(256)
    n = int(x)
    m = int(y)
    def test1():
        x * y
        y * x
    def test2():
        n * m
        m * n
    benchmark(test1, "mul (10k)", 10000)
    benchmark(test2, "mul* (10k)", 10000)

def benchNegate():
    x =  Number.random(256)
    y = -Number.random(256)
    n = int(x)
    m = int(y)
    def test1():
        -x
        -y
    def test2():
        -n
        -m
    benchmark(test1, "negate (10k)", 10000)
    benchmark(test2, "negate* (10k)", 10000)

def benchToString():
    x = Number.random(256)
    y = -x
    n = int(x)
    m = int(y)
    def test1():
        str(x)
        str(y)
    def test2():
        str(n)
        str(m)
    benchmark(test1, "str (10k)", 10000)
    benchmark(test2, "str* (10k)", 10000)



def benchRandom():
    benchmark(lambda : Number.random(256), "random (10k)", 10000)


def benchSign():
    x = Number.random(256)
    y = -x
    n = int(x)
    m = int(y)
    def test1():
        x.sign()
        y.sign()
    benchmark(test1, "sign", 1000000)


def benchCompareTo():
    x = Number.random(256)
    y = Number.random(256)
    n = int(x)
    m = int(y)
    def test1():
        x < y
        y < x
    def test2():
        n < m
        m < n
    benchmark(test1, "compareTo", 1000000)
    benchmark(test2, "compareTo*", 1000000)

def benchHashCode():
    x = Number.random(256)
    n = int(x)
    benchmark(lambda : hash(x), "hash", 1000000)
    benchmark(lambda : hash(n), "hash*", 1000000)

def benchNumberEquals():
    x = Number.random(256)
    y = Number.random(256)
    n = int(x)
    m = int(y)
    def test1():
        x == y
        y == x
    def test2():
        n == m
        m == n
    benchmark(test1, "equals", 1000000)
    benchmark(test2, "equals*", 1000000)


def benchFromBigInteger():
    x = Number.random(256)
    n = int(x)
    m = -n
    def test1():
        Number.fromInt(n)
        Number.fromInt(m)
    benchmark(test1, "fromInt", 1000000)

def benchToInt():
    x = Number.random(256)
    y = -x
    def test1():
        int(x)
        int(y)
    benchmark(test1, "toInt", 1000000)

def benchBitLength():
    x = Number.random(256)
    n = int(x)
    benchmark(lambda : x.bitLength(), "bitLength", 1000000)
    benchmark(lambda : n.bit_length(), "bitLength*", 1000000)


bench = Bench_Number()
bench.run()




