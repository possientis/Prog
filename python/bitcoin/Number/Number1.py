import random as librandom

class Number1(object):

    # static data
    randGen = librandom.SystemRandom()

    def __init__(self, value):
        self.value = value

    def __add__(self, rhs):
        return Number1(self.value + rhs.value)

    def __mul__(self, rhs):
        return Number1(self.value * rhs.value)

    def __neg__(self):
        return Number1(-self.value)

    def __lt__(self, rhs):
        return self.value < rhs.value

    def __le__(self, rhs):
        return self.value <= rhs.value

    def __eq__(self, rhs):
        return self.value == rhs.value

    def __ne__(self, rhs):
        return self.value != rhs.value

    def __ge__(self, rhs):
        return self.value >= rhs.value

    def __gt__(self, rhs):
        return self.value > rhs.value

    def __hash__(self):
        return hash(self.value) + hash(type(self))

    def sign(self):
        if self.value < 0:
            return -1
        elif self.value == 0: 
            return 0
        else:
            return 1

    def toBytes(self, numBytes):
        if self.value >= 0:
            value = self.value
        else:
            value = -self.value
        return value.to_bytes(numBytes, byteorder='big', signed=False)

    def bitLength(self):
        if self.value >= 0:
            value = self.value
        else:
            value = -self.value
        return value.bit_length()

    def __str__(self):
        return str(self.value)
    


ZERO = Number1(0)
ONE  = Number1(1)

def fromInt(x):
    return Number1(x)

def random(numBits):
    if numBits <= 0:
        return ZERO
    else:
        return Number1(Number1.randGen.getrandbits(numBits))

def fromBytes(sign, bytestring):
    value = int.from_bytes(bytestring, byteorder='big', signed=False)
    if sign == 0:
        if value != 0:
            raise ValueError("inconsistent sign argument")
        else:
            return ZERO
    elif sign == 1:
        return Number1(value)
    elif sign == -1:
        return Number1(-value)
    else:
        raise ValueError("invalid sign argument")

