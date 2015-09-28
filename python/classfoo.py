class foo(object):
    # property
    def getBar(self): return 23
    def setBar(self,val): pass
    def delBar(self): pass
    bar = property(getBar, setBar, delBar, "This is my doc")
    # len
    def __len__(self): return 1     # or any other implementation
    # self[key]
    def __getitem__(self,key): return 23 # could also depend on key
    # item in self
    def __contains__(self,item): return True # contains everything
    # add
    def __add__(self,other): return 5
    def __repr__(self) : return "xxx"


x = foo()
print (len(x))  # calls __len__
print(x[2])
print(x['a'])   # call __getitem__)
print(23 in x)  # call __contains__
y = foo()
print(x + y)    # expecting 5
print(hash(x))
print(x)        # xxx
print(hash(int))

