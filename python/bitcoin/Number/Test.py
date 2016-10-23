import Number

_0 = Number.ZERO
_1 = Number.ONE
_2 = _1 + _1
_3 = _2 + _1
_4 = _2 * _2
x = Number.fromInt(345)
y = Number.fromInt(-125)

print(_0)
print(_1)
print(_2)
print(_3)
print(_4)
print(-_4)

print(hash(_4))
print(_4.sign())
print((-_4).sign())
print(_0.sign())
print(x + y)
print('random number = %s' % Number.random(8))
z = Number.fromInt(2**256)
t = -z
print(z)
print(t)
u = z.toBytes(33)
v = t.toBytes(33)

print(u)
print(v)

print(z == Number.fromBytes(1,u))
print(t == Number.fromBytes(-1,u))
print(Number.ZERO == Number.fromBytes(0,u))

print(z.bitLength())
print(t.bitLength())
print(_0.bitLength())
print(_1.bitLength())
print(_2.bitLength())
print(_3.bitLength())
print(_4.bitLength())





