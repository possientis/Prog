#!/usr/bin/python3
import dis

def myFunc():
    y = 23
    return 0


def main():
    dis.dis(myFunc)


if __name__ == '__main__':
    main()
