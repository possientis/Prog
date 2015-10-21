#!/usr/bin/python3
from A import *
from B import *

def main():
    a = A(1)
    b = B(2,3)
    print(repr(a.a)+":"+repr(b.a)+":"+repr(b.b))
    a.foo()
    b.foo()
    c = B(4,5)
    c.foo()

    a1 = A(a)   # copy ctor
    b1 = B(b)   # copy ctor
    print(repr(a1.a)+":"+repr(b1.a)+":"+repr(b1.b))

    a2 = A(2)
    A.swap(a1,a2)
    print(repr(a1.a)+":"+repr(a2.a))

    b2 = B(4,5)
    B.swap(b1,b2)
    print(repr(b1.a)+":"+repr(b1.b)+":"+repr(b2.a)+":"+repr(b2.b));



main()
