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

def main3():
    p = optparse.OptionParser(
        description="Python 'ls' command clone",
        prog="pyls",
        version="0.1a",
        usage="%prog [directory]")

    p.add_option(
        "--verbose", "-v", 
        action="store_true",
        help="Enables Verbose Output",
        default=False)

    p.add_option(
        "--quiet", "-q", 
        action="store_true",
        help="Disables Output",
        default=False)


    options, arguments = p.parse_args()
    if len(arguments) == 1:
        if options.verbose:
            print("Verbose Mode Enabled")
        path = arguments[0]
        for filename in os.listdir(path):
            if options.verbose:
                print("Filename: %s " % filename)
            elif options.quiet:
                pass
            else:
                print(filename)
    else:
        p.print_help()


def main4():
    p = optparse.OptionParser(
        description="Python 'ls' command clone",
        prog="pyls",
        version="0.1a",
        usage="%prog [directory]")

    p.add_option("-v", action="count", dest="verbose")  # -v or -vv or -vvv etc

    options, arguments = p.parse_args()

    if len(arguments) == 1:
        if options.verbose:
            print("Verbose Mode Enabled at Level: %s" % options.verbose)
        path = arguments[0]
        for filename in os.listdir(path):
            if options.verbose == 1:
                print("Filename: %s " % filename)
            elif options.verbose ==2 :
                fullpath = os.path.join(path,filename)
                print(
                    "Filename: %s | Byte Size: %s" % 
                    (filename, os.path.getsize(fullpath)))
            else: 
                print(filename)
    else:
        p.print_help()


def main5():
    p = optparse.OptionParser(
        description="Python 'ls' command clone",
        prog="pyls",
        version="0.1a",
        usage="%prog [directory]")

    p.add_option(
        "--chatty", "-c", 
        action="store", 
        type="choice",
        dest="chatty",
        choices=["normal", "verbose", "quiet"],
        default="normal")

    options, arguments = p.parse_args()

#    print(options)
    if len(arguments) == 1:
        if options.chatty == "verbose":
            print("Verbose Mode Enabled")
        path = arguments[0]
        for filename in os.listdir(path):
            if options.chatty == "verbose":
                print("Filename: %s " % filename)
            elif options.chatty == "quiet":
                pass
            else:
                print(filename)
    else:
        p.print_help()

def main6():
    p = optparse.OptionParser(
        description="Lists contents of two directories",
        prog="pymultils",
        version="0.1a",
        usage="%prog [--dir dir1 dir2]")

    p.add_option("--dir", action="store", dest="dir", nargs=2)

    options, arguments = p.parse_args()

    if options.dir:
        for dir in options.dir:
            print("Listing of %s:\n" % dir)
            for filename in os.listdir(dir):
                print(filename)
    else:
        p.print_help()


if __name__ == '__main__':
#    main1()
#    main2()
#    main3();
#    main4()
#    main5()
    main6()



