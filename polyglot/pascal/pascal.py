#!/usr/bin/python3
# diffcult to follow Scheme or Haskell for Python

from operator import add

def pascal(n):
    if n == 1:
        return [1]
    else:
        return addList(shiftLeft(pascal(n - 1)),
                shiftRight(pascal(n - 1)))

def shiftLeft(seq):
    return seq + [0]

def shiftRight(seq):
    return [0] + seq

def addList(seq1,seq2):
    return list(map(add,seq1,seq2))

def fastPascal(n):
    if n == 1:
        return [1]
    else:
        seq = fastPascal(n - 1)
        return addList(shiftLeft(seq),shiftRight(seq))

print(fastPascal(20))


