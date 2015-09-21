#!/usr/bin/python3
# usage:> ./run.py filename[.java]

import sys
import subprocess

def cleanUpFile(filename):
    cmd = 'rm ' + filename
    (status,output) = subprocess.getstatusoutput(cmd)
    #not testing for failure as file may not exist

def cleanUpAllFiles(filename):
    # cleaning up filename.class file
    cleanUpFile(filename + '.class')

    # cleaning up filename.jar file
    cleanUpFile(filename + '.jar')

    # cleaning up filename.html file
    cleanUpFile(filename + '.html')


def main():

    # checking a single file name given as argument
    if(len(sys.argv) != 2):
        sys.stderr.write('Need a single file name as argument\n')
        sys.exit(1)

    # filename
    filename = sys.argv[1]
    # removing file extension if present
    if filename[-5:] == '.java':
        filename = filename[:-5]

    # cleaning previously created files, if any
    cleanUpAllFiles(filename)

    # compiling filename.java
    cmd = 'javac -classpath acm.jar ' + filename +'.java'
    (status,output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write('Failed to compile ' + filename + '.java\n' + output)
        sys.exit(1)

    # making copy of acm.jar
    cmd = 'cp acm.jar ' + filename + '.jar'
    (status,output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write('Not able to make copy of acm.jar\n' + output)
        sys.exit(1)

    # adding filename.class to archive filename.jar
    cmd = 'jar uf ' + filename + '.jar ' + filename + '.class'
    (status,output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write('Not able to add .class to .jar file\n' + output)
        sys.exit(1)

    # creating filename.html
    fd = open(filename + '.html',"w")

    fd.write('<html><applet archive='+filename+'.jar '
            + 'code='+filename+'.class '
            + 'width=1000 height=600></applet></html>')

    fd.close()

    # launching applet
    cmd = 'appletviewer ' + filename + '.html'
    (status,output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write('Failed to launch applet\n' + output)

    # final cleanup
    cleanUpAllFiles(filename)


if __name__ == '__main__':
    main()

