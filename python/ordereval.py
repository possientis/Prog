#import sys

def main():

    x = 5
    y = 5

    def f():
        x = 0
        return x

    def g():
        y = 0
        return y

    print("Starting with x = 5\n")

    z = f() + x
    t = y + g()

    print("(x=0) + x evaluates to",z)
    print("x + (x=0) evaluates to",t)




if __name__ == '__main__':
    main()

