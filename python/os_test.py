
import sys
import os
#import shutil
import subprocess

#shutil.copy(source,dest)
#os.path.exists('/var')

def List(dirName):
#    cmd = 'ls -l ' + dirName
#    (status,output) = subprocess.getstatusoutput(cmd)
    Filenames = os.listdir(dirName)
    for filename in Filenames:
        path = os.path.join(dirName,filename)
        print(path)
        print(os.path.abspath(path))

def main():
    List(sys.argv[1])






if __name__ == '__main__':
    main()

