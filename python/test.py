#!/usr/bin/python3


class A:
    def foo(self):
        print("Hello world!")



def main():
    a = A()
    a.foo()
    m = a.foo
    print(hex(id(a)))
    print(m.__self__)
    print(m.__func__)





main()
