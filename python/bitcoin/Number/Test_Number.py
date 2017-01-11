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
        checkNegate()
        checkToString()
        checkCompareTo()
        checkHash()
        checkNumberEquals()  
        checkFromInt()
        checkInt()
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
    bs = Number.ONE.toBytes(1)
    checkEquals(len(bs), 1, "checkToBytes.5")
    checkEquals(bs[0], 0x01, "checkToBytes.6")
    bs = (-Number.ONE).toBytes(1)
    checkEquals(len(bs), 1, "checkToBytes.7")
    checkEquals(bs[0], 0x01, "checkToBytes.8")
    bs = Number.ONE.toBytes(32)
    checkEquals(len(bs), 32, "checkToBytes.9")
    checkEquals(bs[31], 0x01, "checkToBytes.10")
    for i in range(0, 31):
        checkEquals(bs[i], 0x00, "checkToBytes.11")

    # random
    x = Number.random(256)
    y = -x
    bs = x.toBytes(32)
    checkEquals(x, Number.fromBytes(1, bs), "checkToBytes.12")
    checkEquals(y, Number.fromBytes(-1, bs), "checkToBytes.13")
    bs = y.toBytes(32)
    checkEquals(x, Number.fromBytes(1, bs), "checkToBytes.14")
    checkEquals(y, Number.fromBytes(-1, bs), "checkToBytes.15")

    
def checkRandom():
    # checking a random generator should be far more involved
    # than anything done here
    x = Number.random(0)
    checkEquals(x, Number.ZERO, "checkRandom.1")
    
    x = Number.random(1)    # single bit
    checkCondition(x == Number.ZERO or x == Number.ONE, "checkRandom.2")

    x = Number.random(256)
    checkEquals(x.sign(), 1, "checkRandom.3")

    count = 0
    for i in range(0, 10000):
        x = Number.random(256)
        bs = x.toBytes(32)
        y = Number.random(5)        # selecting byte 0 to 31
        index = y.toBytes(1)[0]
        test = bs[index]
        z = Number.random(3)        # selectingbit 0...7
        bit = z.toBytes(1)[0]
        if test & (1 << bit):
            count += 1

    checkCondition(count > 4800, "checkRandom.4")
    checkCondition(count < 5200, "checkRandom.5")


def checkAdd():
    x = signedRandom(256)
    y = signedRandom(256)
    z = signedRandom(256)

    # x + 0 = x
    checkEquals(x + Number.ZERO, x, "checkAdd.1")

    # 0 + x = x
    checkEquals(Number.ZERO + x, x, "checkAdd.2")

    # x + (-x) = 0
    checkEquals(x + (-x), Number.ZERO, "checkAdd.3")

    # (-x) + x = 0
    checkEquals((-x) + x, Number.ZERO, "checkAdd.4")

    # x + y = y + x
    checkEquals(x + y, y + x, "checkAdd.5")

    # (x + y) + z = x + (y + z)
    checkEquals((x + y) + z, x + (y + z), "checkAdd.6")

    # actual check of x + y
    n = int(x)
    m = int(y)
    s = n + m
    check = Number.fromInt(s)
    checkEquals(check, x + y, "checkAdd.7")



def checkMul():
    x = signedRandom(256)
    y = signedRandom(256)
    z = signedRandom(256)

    # x * 0 = 0
    checkEquals(x * Number.ZERO, Number.ZERO, "checkMul.1")

    # 0 * x = 0
    checkEquals(Number.ZERO * x, Number.ZERO, "checkMul.2")

    # x * 1 = x
    checkEquals(x * Number.ONE, x, "checkMul.3")

    # 1 * x = x
    checkEquals(Number.ONE * x, x, "checkMul.4")

    # (-x) * (-y) = x * y
    checkEquals((-x) * (-y), x * y, "checkMul.5")

    # x * y = y * x
    checkEquals(x * y, y * x, "checkMul.6")

    # (x * y) * z = x * (y * z)
    checkEquals((x * y) * z, x * (y * z), "checkMul.7")

    # (x + y) * z = (x * z) + (y * z)
    checkEquals((x + y) * z, (x * z) + (y * z), "checkMul.8")

    # actual check of x + y
    n = int(x)
    m = int(y)
    p = n * m
    check = Number.fromInt(p)
    checkEquals(check, x * y, "checkMul.9")

def checkNegate():
    x = signedRandom(256)
    y = -x

    # x + (-x) = 0
    checkEquals(Number.ZERO, x + y, "checkNegate.1")

    # actual check
    n = int(x)
    z = Number.fromInt(-n)
    checkEquals(y, z, "checkNegate.2")


def checkToString():
    # zero
    check1 = str(Number.ZERO)
    checkEquals(check1, "0", "checkToString.1")

    # one
    check1 = str(Number.ONE)
    checkEquals(check1, "1", "checkToString.2")

    # minus one
    check1 = str(-Number.ONE)
    checkEquals(check1, "-1", "checkToString.3")

    # random positive
    x = Number.random(256)
    check1 = str(x)
    check2 = str(int(x))
    checkEquals(check1, check2, "checkToString.4")



def checkCompareTo():
    # from random
    x = Number.random(256)
    y = -x
    checkCondition(x > Number.ZERO, "checkCompareTo.1")
    checkCondition(Number.ZERO < x, "checkCompareTo.2")
    checkCondition(y < Number.ZERO, "checkCompareTo.3")
    checkCondition(Number.ZERO > y, "checkCompareTo.4")

    # from bytes
    bs = getRandomBytes(32)
    x = Number.fromBytes(1, bs)
    y = Number.fromBytes(-1, bs)
    checkCondition(x > Number.ZERO, "checkCompareTo.5")
    checkCondition(Number.ZERO < x, "checkCompareTo.6")
    checkCondition(y < Number.ZERO, "checkCompareTo.7")
    checkCondition(Number.ZERO > y, "checkCompareTo.8")

    # from signedRandom
    x = signedRandom(256)
    y = signedRandom(256)
    n = int(x)
    m = int(y)
    checkEquals(x < y, n < m, "checkCompareTo.9")
    checkEquals(y < x, m < n, "checkCompareTo.10")
    y = Number.fromInt(n)
    checkCondition(x == y, "checkCompareTo.11")
    checkCondition(y == x, "checkCompareTo.12")

    # 0 < 1
    checkCondition(Number.ZERO < Number.ONE, "checkCompareTo.13")
    checkCondition(Number.ONE > Number.ZERO, "checkCompareTo.14")


def checkHash():
    # 0 and 1
    hash1 = hash(Number.ZERO)
    hash2 = hash(Number.ONE)
    checkCondition(hash1 != hash2, "checkHash.1")

    # x and -x
    x = signedRandom(256)
    hash1 = hash(x)
    hash2 = hash(-x)
    checkCondition(hash1 != hash2, "checkHash.2")

    # same number
    n = int(x)
    y = Number.fromInt(n)
    hash1 = hash(x)
    hash2 = hash(y)
    checkEquals(hash1, hash2, "checkHash.3")


def checkNumberEquals():
    # 0 and 1
    checkCondition(not Number.ZERO == Number.ONE, "checkNumberEquals.1")
    checkCondition(Number.ZERO != Number.ONE, "checkNumberEquals.2")
    checkCondition(not Number.ONE == Number.ZERO, "checkNumberEquals.3")
    checkCondition(Number.ONE != Number.ZERO, "checkNumberEquals.4")

    # x and -x
    x = signedRandom(256)
    checkCondition(not x == -x, "checkNumberEquals.5")
    checkCondition(x != -x, "checkNumberEquals.6")

    # same number
    n = int(x)
    y = Number.fromInt(n)
    checkCondition(x == y, "checkNumberEquals.7")
    checkCondition(not x != y, "checkNumberEquals.8")
    checkCondition(y == x, "checkNumberEquals.9")
    checkCondition(not y != x, "checkNumberEquals.10")
    checkCondition(x == x, "checkNumberEquals.11")
    checkCondition(not x != x, "checkNumberEquals.12")
    checkEquals(x, y, "checkNumberEquals.13")
    checkEquals(y, x, "checkNumberEquals.14")
    checkEquals(x, x, "checkNumberEquals.15")


def checkFromInt():
    # 0
    x = Number.fromInt(0)
    y = Number.ZERO
    checkEquals(x, y, "checkFromInt.1")

    # 1
    x = Number.fromInt(1)
    y = Number.ONE
    checkEquals(x, y, "checkFromInt.2")

    # signed random
    x = signedRandom(256)
    y = Number.fromInt(int(x))
    checkEquals(x, y, "checkFromInt.3")



def checkInt():
    # 0
    n = int(Number.ZERO)
    m = 0
    checkEquals(n, m, "checkInt.1")

    # 1
    n = int(Number.ONE)
    m = 1
    checkEquals(n, m, "checkInt.2")

    # signed random
    x = signedRandom(256)
    n = int(x)
    m = int.from_bytes(x.toBytes(32), byteorder='big', signed=False)
    m = m * x.sign()
    checkEquals(n, m, "checkInt.3")


def checkBitLength():
    # 0
    check1 = Number.ZERO.bitLength()
    checkEquals(check1, 0, "checkBitLength.1")

    # 1
    check1 = Number.ONE.bitLength()
    checkEquals(check1, 1, "checkBitLength.2")

    # -1
    check1 = (-Number.ONE).bitLength()
    checkEquals(check1, 1, "checkBitLength.3")

    # 2
    _2 = Number.ONE+ Number.ONE
    check1 = _2.bitLength()
    checkEquals(check1, 2, "checkBitLength.4")

    # -2
    check1 = (-_2).bitLength()
    checkEquals(check1, 2, "checkBitLength.5")

    # 4
    _4 = _2 * _2
    check1 = _4.bitLength()
    checkEquals(check1, 3, "checkBitLength.6")

    # -4
    check1 = (-_4).bitLength()
    checkEquals(check1, 3, "checkBitLength.7")

    # 16
    _16 = _4 * _4
    check1 = _16.bitLength()
    checkEquals(check1, 5, "checkBitLength.8")

    # -16
    check1 = (-_16).bitLength()
    checkEquals(check1, 5, "checkBitLength.8")

    # 256
    _256 = _16 * _16
    check1 = _256.bitLength()
    checkEquals(check1, 9, "checkBitLength.10")

    # -256
    check1 = (-_256).bitLength()
    checkEquals(check1, 9, "checkBitLength.11")

    # +- 2^256
    zero = 0
    bs = zero.to_bytes(32, byteorder='big', signed=False) 
    bs = b'\x01' + bs 
    x = Number.fromBytes(1, bs)
    y = Number.fromBytes(-1, bs)
    checkEquals(x.bitLength(), 257, "checkBitLength.12")
    checkEquals(y.bitLength(), 257, "checkBitLength.13")

    
test = Test_Number()
test.run()
