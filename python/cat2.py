#!/usr/bin/python3

import sys

def cat(filename):
    f = open(filename,'rU')
    lines = f.readlines()
    print(lines)
    f.close()



def main():
    cat(sys.argv[1])


if __name__ == '__main__':
    main()

