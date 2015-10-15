from A import *

class B(A):
    def __init__(self,a,b):
        A.__init__(self,a)
        self.b = b
    def foo(self):
        print("B::foo() is running")
