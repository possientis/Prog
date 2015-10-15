from A import *

class B(A):
    def __init__(self,a,b = None):
        if b == None:               # copy ctor
            assert isinstance(a,B)  # sole argument must be other B object
            A.__init__(self,a)
            self.b = a.b
        else:                   # normal ctor
            assert isinstance(a,int)
            assert isinstance(b,int)
            A.__init__(self,a)
            self.b = b

    def foo(self):
        print("B::foo() is running")
