import Number
from Test_Abstract import *

class Test_Number(Test_Abstract):
    
    def run(self):
        logMessage("Number unit test running ...")
        checkZERO()
        checkONE()
        checkFromBytes()
        checkSign()
        checkToBytes()
        checkRandom()
        checkAdd()
        checkMul()
        checkToString()
        checkCompareTo()
        checkHashCode()
        checkNumberEquals()  
        checkFromBigInteger()
        checkToBigInteger()
        checkBitLength()

def signedRandom(numBits):
    x = Number.random(numBits)
    flip = Number.random(1)
    if flip == Number.ONE: 
        return -x 
    else: 
        return x


def checkZERO():
    zero = Number.ZERO
    x = Number.random(256)
    y = zero + x
    z = x + zero
    checkEquals(x, y, "checkZERO.1")
    checkEquals(x, z, "checkZERO.2")


def checkONE():
    one = Number.ONE
    x = Number.random(256)
    y = one * x
    z = x * one
    checkEquals(x, y, "checkONE.1")
    checkEquals(x, z, "checkONE.2")


def checkFromBytes():
    eName = "ValueError"

    # empty byte string
    b0 = b''    # empty byte string
    x = Number.fromBytes(1, b0)
    checkEquals(x, Number.ZERO, "checkFromBytes.1")
    x = Number.fromBytes(-1, b0)
    checkEquals(x, Number.ZERO, "checkFromBytes.2")
    x = Number.fromBytes(0, b0)
    checkEquals(x, Number.ZERO, "checkFromBytes.3")
    checkException(lambda : Number.fromBytes(2, b0), eName,"checkFromBytes.4")
    checkException(lambda : Number.fromBytes(-2, b0), eName,"checkFromBytes.5")

    # single 0x00 byte
    b1 = b'\x00'
    x = Number.fromBytes(1, b1)
    checkEquals(x, Number.ZERO, "checkFromBytes.6")
    x = Number.fromBytes(-1, b1)
    checkEquals(x, Number.ZERO, "checkFromBytes.7")
    x = Number.fromBytes(0, b1)
    checkEquals(x, Number.ZERO, "checkFromBytes.8")
    checkException(lambda : Number.fromBytes(2, b1), eName,"checkFromBytes.9")
    checkException(lambda : Number.fromBytes(-2, b1), eName,"checkFromBytes.10")

    # two 0x00 bytes
    b2 = b'\x00\x00'
    x = Number.fromBytes(1, b2)
    checkEquals(x, Number.ZERO, "checkFromBytes.11")
    x = Number.fromBytes(-1, b2)
    checkEquals(x, Number.ZERO, "checkFromBytes.12")
    x = Number.fromBytes(0, b2)
    checkEquals(x, Number.ZERO, "checkFromBytes.13")
    checkException(lambda : Number.fromBytes(2, b2), eName,"checkFromBytes.14")
    checkException(lambda : Number.fromBytes(-2, b2), eName,"checkFromBytes.15")

    # single 0x01 byte
    b3 = b'\x01'
    x = Number.fromBytes(1, b3)
    checkEquals(x, Number.ONE, "checkFromBytes.16")
    checkException(lambda : Number.fromBytes(0, b3), eName,"checkFromBytes.17")

    # x + (-x) = 0
    b4 = getRandomBytes(32)
    x = Number.fromBytes(1, b4)
    y = Number.fromBytes(-1, b4)
    z = x + y
    checkEquals(z, Number.ZERO, "checkFromBytes.18")

    # multiplying by -1
    z = Number.fromBytes(-1, b3)    # -1
    z = z * x
    checkEquals(y, z, "checkFromBytes.19")

    # padding with 0x00 bytes
    b5 = getRandomBytes(28)
    x = Number.fromBytes(1, b5)
    y = Number.fromBytes(-1, b5)
    b6 = b'\x00\x00\x00\x00' + b5
    z = Number.fromBytes(1, b6)
    checkEquals(x, z, "checkFromBytes.20")
    z = Number.fromBytes(-1, b6)
    checkEquals(y, z, "checkFromBytes.21")

    # actual replication
    b7 = getRandomBytes(32)
    b8 = b'\xFF'
    _256 = Number.fromBytes(1, b8) + Number.ONE
    x = Number.fromBytes(1, b7)
    y = Number.fromBytes(-1, b7)
    z = Number.ZERO
    t = Number.ZERO
    for i in range(0,32):
        b8 = b7[i].to_bytes(1, byteorder='big')
        z = (z * _256) + Number.fromBytes(1, b8)
        t = (t * _256) + Number.fromBytes(-1, b8)
    checkEquals(x, z, "checkFromBytes.22")
    checkEquals(y, t, "checkFromBytes.23")


    # using toBytes and sign
    b9 = getRandomBytes(32)
    x = Number.fromBytes(1, b9)
    y = Number.fromBytes(-1, b9)

    checkEquals(x.sign(), 1, "checkFromBytes.24")
    checkEquals(y.sign(), -1, "checkFromBytes.25")

    b10 = x.toBytes(32) 
    b11 = y.toBytes(32)

    checkEquals(b9, b10, "checkFromBytes.26")
    checkEquals(b9, b11, "checkFromBytes.27")


def checkSign():
    checkEquals(Number.ZERO.sign(), 0, "checkSign.1")
    b = getRandomBytes(32)
    x = Number.fromBytes(1, b)
    y = Number.fromBytes(-1, b)
    checkEquals(x.sign(), 1, "checkSign.2")
    checkEquals(y.sign(), -1, "checkSign.3")



def checkToBytes():
    eName = "OverflowError"

    # ZERO
    bs = Number.ZERO.toBytes(0)
    checkEquals(len(bs), 0, "checkToBytes.1")

    bs = Number.ZERO.toBytes(32)
    checkEquals(len(bs), 32, "checkToBytes.2")
    for i in range(0, 32):
        checkEquals(bs[i], 0x00, "checkToBytes.3")

    # ONE
    checkException(lambda : Number.ONE.toBytes(0), eName, "checkToBytes.4")


def checkRandom(): pass # TODO
def checkAdd(): pass # TODO
def checkMul(): pass # TODO
def checkToString(): pass # TODO
def checkCompareTo(): pass # TODO
def checkHashCode(): pass # TODO
def checkNumberEquals()  : pass # TODO
def checkFromBigInteger(): pass # TODO
def checkToBigInteger(): pass # TODO
def checkBitLength(): pass # TODO


test = Test_Number()
test.run()
