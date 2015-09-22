#!/usr/bin/python3

#import sys

def foo():
    def bar():
        def baz():
            return 1
        return baz()
    return bar()

def main():
    print(foo())

if __name__ == '__main__':
    main()


