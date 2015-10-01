class X(object):
    def __call__(self):
        foo()

def foo():
    print("foo is running")


def main():
    x = X() # creating instance
    x()     # calling instance (callable object since __call__ defined)

if __name__ == "__main__":
    main()
