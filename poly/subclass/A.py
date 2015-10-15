class A:
    def __init__(self, a):
        if isinstance(a,A): # copy ctor
            self.a = a.a
        else:               # normal ctor
            assert isinstance(a,int)
            self.a = a

    def foo(self):
        print("A::foo() is running")
