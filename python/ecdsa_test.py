import ecdsa
import random
import codecs

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
    random_char = lambda: chr(random.randint(0,255))
    def convert_to_int(array): 
        return int(codecs.encode("".join(array).encode('utf-8'),'hex_codec'),16)
    byte_array = [random_char() for i in range(32)]
    return byte_array

string1 = "".join(random_secret()).encode('utf-8')
string2 = codecs.encode(bytes(string1), 'hex_codec')


