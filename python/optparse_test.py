# the right option to build command line tools
import optparse
import os

def main1():
    p = optparse.OptionParser()
    p.add_option('--sysadmin', '-s', default='BOFH')
    options, arguments = p.parse_args()
    print('Hello, %s' % options.sysadmin)
    print('This is the list of arguments %s:' % arguments)


def main2():
    p = optparse.OptionParser(
        description="Python 'ls' command clone",
        prog='pyls',
        version='0.1a',
        usage='%prog [directory]')

    options, arguments = p.parse_args()
    if len(arguments) == 1:
        path = arguments[0]
        for filename in os.listdir(path):
            print(filename)
    else:
        p.print_help()


if __name__ == '__main__':
#    main1()
    main2()
