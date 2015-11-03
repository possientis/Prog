
def double(f):
    def newFunc(x):
        return 2*f(x)
    return newFunc

@double
def h(x):
    return x + 3


print("Hello world!")
print(h(7))
