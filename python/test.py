#!/usr/bin/python3

#import sys

def gmap(func,iterable):
    for item in iterable:
        yield func(item)
def map(func,iterable):
    return list(gmap(func,iterable))

def main():
    print('Main is now running...\n')

if __name__ == '__main__':
    main()

