#!/usr/bin/python3

import sys
import os
#import shutil
import subprocess

#shutil.copy(source,dest)
#os.path.exists('/var')

def List(dirName):
    cmd = 'ls l ' + dirName
    (status,output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write('there was an error: ' + output)
        sys.exit(1)

    print('This is not running\n')
    print(output)

def main():
    List(sys.argv[1])






if __name__ == '__main__':
    main()

