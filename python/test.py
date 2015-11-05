#!/usr/bin/python3


class A:
    def foo(x,y):
        return y



def main():
    a = A()
    print(a.foo(10))
    print(A.foo(3,20))




main()
