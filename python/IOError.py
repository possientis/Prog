import sys

def cat(filename):
    try:
        f = open(filename,'rU')
        text = f.read()
        print(text)
        f.close()
    except IOError:
        print('IO Error\n')




def main():
    cat(sys.argv[1])


if __name__ == '__main__':
    print('Launching main ...\n')
    main()

