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


main()
