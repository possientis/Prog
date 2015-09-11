#!/usr/bin/pyhton3

class Base(object):
    def getFoo(self): return 23
    foo = property(getFoo, doc = "the foo property ...")

class Derived(Base):
    def getFoo(self): return 42

class Base2(object):
    def getFoo(self): return 23
    def _fooget(self): return self.getFoo()
    foo = property(_fooget, doc = "the foo property ...")

class Derived2(Base2):
    def getFoo(self): return 42


def main():
    d = Derived()
    print(d.foo)
    e = Derived2()
    print(e.foo)


if __name__ == '__main__':
    main()
