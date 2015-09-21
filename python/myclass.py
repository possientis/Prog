#!/usr/bin/python3

class X(object):
    foo = 0
    def __init__(self,i):
        self.foo = i
        return
    def __repr__(self):
        return "<object of type X: foo = " + str(self.foo) + " >"
    def __str__(self):
        return self.__repr__()
    def __lt__(self,y):
        return (self.foo < y.foo)





def main():
    x = X(3)
    print(x.foo)
    print(x.__repr__())
    print(x)
    print(x < X(5))


if __name__ == '__main__':
    main()



