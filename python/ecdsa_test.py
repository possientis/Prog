import ecdsa
import random

_p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
_r = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
_b = 0x0000000000000000000000000000000000000000000000000000000000000007
_a = 0x0000000000000000000000000000000000000000000000000000000000000000
_Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
_Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

curve_secp256k1 = ecdsa.ellipticcurve.CurveFp(_p,_a,_b)

# how do I know the order of the secp256k1 group.
# how do I know that G is indeed a generator of this group
generator_secp256k1 = ecdsa.ellipticcurve.Point(curve_secp256k1, _Gx, _Gy, _r)

oid_secp256k1 = (1, 3, 132, 0, 10)  # what is that?
SECP256k1 = ecdsa.curves.Curve(
    "SECP256k1", curve_secp256k1, generator_secp256k1, oid_secp256k1
)
ec_order = _r
curve = curve_secp256k1
generator = generator_secp256k1

def random_secret():
    # use cryptographically secure PRNG for real application
    random_char = lambda: random.randint(0,255)         
    byte_array = [random_char() for i in range(32)]
    byte_string = bytes(byte_array)
    # endianness interpretation of random data does not matter
    return int.from_bytes(byte_string, byteorder='big')

def get_point_pubkey(point):
    if point.y() & 1:
        key = '03' + '%064x' % point.x()
    else:
        key = '02' + '%064x' % point.x()
    return int(key, 16)

def get_point_pubkey_uncomp(point):
    key = '04' + '%064x' % point.x() + '%064x' % point.y()
    return int(key,16)


# example secret key from Mastering Bitcoin
secret1 = 0x1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD  
point1 = secret1 * generator    # main functionality
pubkey1 = get_point_pubkey(point1)
pubkey1_uncomp = get_point_pubkey_uncomp(point1)
check1 = 0x03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a
check2 = 0x04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb
 
assert pubkey1 == check1
assert pubkey1_uncomp == check2


secret = random_secret()
point = secret * generator      # main functionality
pubkey = get_point_pubkey(point)
pubkey_uncomp = get_point_pubkey_uncomp(point)

check3 = ecdsa.ellipticcurve.Point(curve, point.x(), point.y(), ec_order) 
assert point == check3







