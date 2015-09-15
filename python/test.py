#!/usr/bin/python3

#import sys

def doubleUs(x,y):
    return doubleMe(x) + doubleMe(y)

def main():
    print(doubleUs(4,9))

def doubleMe(x):
    return x + x

if __name__ == '__main__':
    main()


