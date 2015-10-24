from A import *

class B(A):
    def __init__(self,a,b = None):
        if b is None:               # copy ctor
            assert isinstance(a,B)  # sole argument must be other B object
            A.__init__(self,a)
            self.b = a.b
        else:                   # normal ctor
            assert isinstance(a,int)
            assert isinstance(b,int)
            A.__init__(self,a)
            self.b = b

    @property
    def b(self):
        return self.__b

    @b.setter
    def b(self,value):
        self.__b = value

    def foo(self):
        print("B::foo() is running")

    def swap(x,y):
        A.swap(x,y)
        temp = x.b; x.b = y.b; y.b = temp
