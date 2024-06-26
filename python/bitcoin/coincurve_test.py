import coincurve

print(dir(coincurve))


#['Context', 'GLOBAL_CONTEXT', 'PrivateKey', 'PublicKey', '__builtins__', '__cached__', '__doc__', '__file__', '__loader__', '__name__', '__package__', '__path__', '__spec__', '_libsecp256k1', 'context', 'ecdsa', 'flags', 'keys', 'utils', 'verify_signature']

bytes1 = bytes([0x03,
                0xf0,0x28,0x89,0x2b,0xad,0x7e,0xd5,0x7d,
                0x2f,0xb5,0x7b,0xf3,0x30,0x81,0xd5,0xcf,
                0xcf,0x6f,0x9e,0xd3,0xd3,0xd7,0xf1,0x59,
                0xc2,0xe2,0xff,0xf5,0x79,0xdc,0x34,0x1a])

pub = coincurve.PublicKey(bytes1)
