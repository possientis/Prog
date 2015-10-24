class A:
    def __init__(self, a):
        if isinstance(a,A): # copy ctor
            self.a = a.a
        else:               # normal ctor
            assert isinstance(a,int)
            self.a = a

    # Like C#, Python offers support for properties
    @property
    def a(self):
        return self.__a

    @a.setter
    def a(self,value):
        self.__a = value


    def foo(self):
        print("A::foo() is running")

    def swap(x,y):  # class member (static member) no 'self'
        temp = x.a; x.a = y.a; y.a = temp
