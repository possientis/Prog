#!/usr/bin/python3
import sys

def cat(filename):
    f = open(filename,'rU')
    text = f.read()
    f.close()
    print(text)



def main():
    cat(sys.argv[1])


if __name__ == '__main__':
    main()

