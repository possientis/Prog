import sys

def Hello(name):

    if name == 'Alice' or name == 'Bob':
        name = name + '???'
    else:
        DoesNotExist(name)

    name = name + '!!!!!!'
    print('Hello', name)

def main():
    Hello(sys.argv[1])

if __name__ == '__main__':
    main()

